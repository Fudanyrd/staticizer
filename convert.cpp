#include <elf.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

namespace
{

void
defer_close (int *fd)
{
  (void)close (*fd);
}

/**
 * Hash function for null-terminated strings.
 */
struct StringHash
{
  size_t
  operator() (const char *dat) const
  {
    const unsigned char *s = (const unsigned char *)dat;
    /* GNU hash impl. */
    size_t ret = 5381;
    for (; *s; s++)
      {
        ret += ret * 32 + *s;
      }
    return ret;
  }
};

struct StringTable
{
  std::unordered_map<std::string, size_t> map;
  /**
   * Starting from 1 because 0 is reserved for the null string.
   */
  size_t next_index;

  size_t
  add (const std::string &str)
  {
    if (__builtin_expect (str.empty (), false))
      {
        return 0;
      }
    auto iter = map.find (str);
    if (iter != map.end ())
      {
        return iter->second;
      }
    size_t idx = next_index;
    map[str] = idx;
    next_index += str.size () + 1; /* +1 for null terminator */
    return idx;
  }
  StringTable () : map (), next_index (1) {}

  size_t
  size () const
  {
    return next_index;
  }

  /**
   * Get the data of the string table.
   * @return The data of the string table.
   */
  std::vector<char>
  data () const
  {
    std::vector<char> ret (next_index, (char)0);
    for (const auto &pair : map)
      {
        const std::string &str = pair.first;
        size_t idx = pair.second;
        assert (idx < next_index);
        memcpy (ret.data () + idx, str.c_str (), str.size ());
      }
    return ret;
  }
};

} /* (anonymous namespace) */

__attribute__ ((noreturn, cold)) static void
die (const char *s)
{
  fputs (s, stderr);
  exit (1);
}

extern "C"
{
  /**
   * In-memory representation of a symbol table entry.
   */
  struct Sym
  {
    const char *name;
    Elf64_Addr value;
    Elf64_Xword size;
    unsigned char info;
    unsigned char other;
    unsigned char shndx_is_udf;
  };
  struct Rela
  {
    Sym *sym;
    Elf64_Addr offset;
    Elf64_Xword type; /* reloc type */
    Elf64_Sxword addend;
  };
} /* C */

namespace
{

/**
 * Partition syms such that the front segment of
 * `syms` are evaluated to true by predicate.
 * This is performed in-place and the field Rela::sym
 * still points to the correct symbol (although the
 * pointer value may change).
 *
 * After partition, symbol appears in the same
 * order as the original input.
 */
template <typename Pred>
void
partition_sym_and_rela (std::vector<Sym> &syms, std::vector<Rela> &relas,
                        const Pred &pred)
{
  const size_t num_syms = syms.size ();

  /* Remember the original index of the symbol referenced by each
     relocation, since the pointers will be invalidated once `syms` is
     reordered. `num_syms` is used as a sentinel for symbol-less relocations.
   */
  std::vector<size_t> rela_sym_idx (relas.size ());
  for (size_t i = 0; i < relas.size (); i++)
    {
      rela_sym_idx[i] = relas[i].sym == nullptr
                            ? num_syms
                            : (size_t)(relas[i].sym - syms.data ());
    }

  /* Stable-partition the indices so that the relative order of symbols is
     preserved. */
  std::vector<size_t> perm (num_syms);
  for (size_t i = 0; i < num_syms; i++)
    {
      perm[i] = i;
    }
  std::stable_partition (
      perm.begin (), perm.end (),
      [&syms, &pred] (size_t idx) { return pred (syms[idx]); });

  /* new_idx[old] is the position `old` ends up at after partitioning. */
  std::vector<size_t> new_idx (num_syms);
  for (size_t i = 0; i < num_syms; i++)
    {
      new_idx[perm[i]] = i;
    }

  /* Apply the permutation to `syms` in place. */
  std::vector<Sym> old_syms = std::move (syms);
  syms.resize (num_syms);
  for (size_t i = 0; i < num_syms; i++)
    {
      syms[i] = old_syms[perm[i]];
    }

  /* Repoint relocations at their new location. */
  for (size_t i = 0; i < relas.size (); i++)
    {
      if (relas[i].sym != nullptr)
        {
          relas[i].sym = syms.data () + new_idx[rela_sym_idx[i]];
        }
    }
}

struct SymIsLocalBind
{
  bool
  operator() (const Sym &sym) const
  {
    return ELF64_ST_BIND (sym.info) == STB_LOCAL;
  }
};

/**
 * A single `.dynobj.N` output section derived from a group of
 * loadable segments sharing the same writability.
 */
struct DynobjInput
{
  std::string name;
  bool writable;
  const unsigned char *data;
  size_t size;
  Elf64_Addr vaddr;
};

struct RelocableFileBuilder
{
  std::vector<Sym> syms;
  std::vector<Rela> relas;
  std::vector<DynobjInput> dynobjs;
  std::vector<Elf64_Addr> init_array;
  std::vector<Elf64_Addr> fini_array;
  /* Section index of the first `.dynobj.N` section (set by dump). */
  int dynobj_first_idx;

  explicit RelocableFileBuilder (std::vector<DynobjInput> dynobj_inputs)
      : syms (), relas (), dynobjs (std::move (dynobj_inputs)),
        dynobj_first_idx (1)
  {
  }

  static Elf64_Word
  reloc_type_convert (Elf64_Word orig_type)
  {
    if (orig_type == R_X86_64_GLOB_DAT || orig_type == R_X86_64_JUMP_SLOT)
      {
        return R_X86_64_64;
      }
    return orig_type;
  }

  /**
   * Section index holding `addr`, or 0 if the address is not covered by
   * any `.dynobj` section.
   */
  int
  section_index_of (Elf64_Addr addr) const
  {
    for (size_t i = 0; i < dynobjs.size (); i++)
      {
        if (addr >= dynobjs[i].vaddr
            && addr < dynobjs[i].vaddr + dynobjs[i].size)
          {
            return dynobj_first_idx + (int)i;
          }
      }
    return 0;
  }

  /**
   * Index into `dynobjs` of the section holding `addr`, or -1.
   */
  int
  dynobj_slot_of (Elf64_Addr addr) const
  {
    for (size_t i = 0; i < dynobjs.size (); i++)
      {
        if (addr >= dynobjs[i].vaddr
            && addr < dynobjs[i].vaddr + dynobjs[i].size)
          {
            return (int)i;
          }
      }
    return -1;
  }

  void dump (const char *opath);
};

std::string
gen_uniq_name (const StringTable &strtab, const char *prefix)
{
  char buf[64] = { 0 };
  strcpy (buf, prefix);
  int prefix_len = strlen (prefix);

  unsigned int suffix = 0;
  while (suffix < 65536)
    {
      sprintf (buf + prefix_len, "_%04x", suffix);
      if (strtab.map.find (buf) == strtab.map.end ())
        {
          return std::string (buf);
        }
      suffix++;
    }

  /* Almost unlikely */
  die ("failed to generate unique name\n");
}

void
RelocableFileBuilder::dump (const char *opath)
{
  std::vector<Elf64_Shdr> shdrs;
  static Elf64_Shdr NULL_ENT; /* DO NOT MUT */
  static Elf64_Sym NULL_SYM;  /* DO NOT MUT */
  shdrs.push_back (NULL_ENT);
  StringTable shstrtab;

  const size_t num_dynobjs = dynobjs.size ();
  assert (num_dynobjs > 0);

  /* Build the `.dynobj.N` sections, one per writability group. */
  const int dynobj_section_index = shdrs.size (); /* which is 1 */
  dynobj_first_idx = dynobj_section_index;
  for (const DynobjInput &dynobj : dynobjs)
    {
      Elf64_Shdr shdr;
      shdr.sh_name = shstrtab.add (dynobj.name);
      shdr.sh_type = SHT_PROGBITS;
      shdr.sh_flags
          = SHF_ALLOC | (dynobj.writable ? SHF_WRITE : SHF_EXECINSTR);
      shdr.sh_addr = 0;
      shdr.sh_offset = 0; /* will be filled later */
      shdr.sh_size = dynobj.size;
      shdr.sh_link = 0;
      shdr.sh_info = 0;
      shdr.sh_addralign = 0x1000;
      shdr.sh_entsize = 0;
      shdrs.push_back (shdr);
    }

  StringTable strtab;
  std::vector<Elf64_Sym> symtab;
  symtab.push_back (NULL_SYM);
  /* One relocation table per `.dynobj.N` section. */
  std::vector<std::vector<Elf64_Rela> > dynobj_rela_tabs (num_dynobjs);
  /* Symbol for init and fini function. */
  std::vector<Elf64_Rela> init_relas; /* .rela.init_array */
  std::vector<Elf64_Rela> fini_relas; /* .rela.fini_array */
  {
    auto build_sym_and_rela_for_entr =
        [this, &symtab, &strtab] (std::vector<Elf64_Rela> &relas,
                                  const char *name_prefix, Elf64_Addr entry) {
          Elf64_Xword sym_idx = symtab.size ();
          Elf64_Rela rela;
          rela.r_addend = 0;
          rela.r_info = ELF64_R_INFO (sym_idx, R_X86_64_64);
          rela.r_offset = (/* count of existing array entrs */ relas.size ())
                          * (sizeof (Elf64_Addr));
          Elf64_Sym s;

          s.st_name
              = strtab.add (gen_uniq_name (strtab, name_prefix).c_str ());
          s.st_info = ELF64_ST_INFO (STB_LOCAL, STT_FUNC); /* LOCAL + FUNC */
          s.st_other = STV_DEFAULT;
          s.st_shndx = (Elf64_Half)section_index_of (entry);
          s.st_value = entry;
          s.st_size = 0; /* UNKNOWN */

          relas.push_back (rela);
          symtab.push_back (s);
        };

    for (Elf64_Addr entry : init_array)
      {
        build_sym_and_rela_for_entr (init_relas, "_init", entry);
      }
    for (Elf64_Addr entry : fini_array)
      {
        build_sym_and_rela_for_entr (fini_relas, "_fini", entry);
      }
    assert (fini_relas.size () == fini_array.size ());
    assert (init_relas.size () == init_array.size ());
  }

  const int dynobj_symbols_start_idx = symtab.size ();
  for (const Sym &sym : syms)
    {
      auto name = strtab.add (sym.name);
      const int sect_idx = section_index_of (sym.value);
      const auto dynobj_sect_idx = dynobj_slot_of (sym.value);
      Elf64_Sym s;
      s.st_name = name;
      s.st_info = sym.info;
      s.st_other = sym.other;
      s.st_shndx = sym.shndx_is_udf ? 0 : (Elf64_Half)sect_idx;
      /**
       * For object file, the `st_value` field is the offset of the symbol from
       * the beginning of of its section.
       */
      s.st_value = sym.value - dynobjs[dynobj_sect_idx].vaddr;
      s.st_size = sym.size;
      symtab.push_back (s);
    }
  for (const Rela &rela : relas)
    {
      int slot = dynobj_slot_of (rela.offset);
      if (slot < 0)
        {
          die ("relocation offset lies outside all .dynobj sections\n");
        }
      Elf64_Xword sym_idx = 0;
      if (rela.sym)
        {
          sym_idx = rela.sym - syms.data ();
          /* Add offset to the index of the first symbol in .dynobj section. */
          sym_idx += dynobj_symbols_start_idx;
        }
      Elf64_Rela r;
      /* `r_offset` is relative to the beginning of the containing section. */
      r.r_offset = rela.offset - dynobjs[slot].vaddr;
      r.r_info = ELF64_R_INFO (sym_idx, reloc_type_convert (rela.type));
      r.r_addend = rela.addend;
      dynobj_rela_tabs[slot].push_back (r);
    }

  /* Build .init_array section if .init is present. */
  const int init_section_index = shdrs.size ();
  if (!init_array.empty ())
    {
      Elf64_Shdr shdr;
      shdr.sh_name = shstrtab.add (".init_array");
      shdr.sh_type = SHT_INIT_ARRAY;
      shdr.sh_flags = SHF_ALLOC | SHF_WRITE;
      shdr.sh_addr = 0;
      shdr.sh_offset = 0; /* will be filled later */
      shdr.sh_size = sizeof (void *) * init_array.size ();
      shdr.sh_link = 0;
      shdr.sh_info = 0;
      shdr.sh_addralign = sizeof (void *);
      shdr.sh_entsize = sizeof (void *);
      shdrs.push_back (shdr);
    }

  /* Build .fini_array section if .fini is present. */
  const int fini_section_index = shdrs.size ();
  if (!fini_array.empty ())
    {
      Elf64_Shdr shdr;
      shdr.sh_name = shstrtab.add (".fini_array");
      shdr.sh_type = SHT_FINI_ARRAY;
      shdr.sh_flags = SHF_ALLOC | SHF_WRITE;
      shdr.sh_addr = 0;
      shdr.sh_offset = 0; /* will be filled later */
      shdr.sh_size = sizeof (void *) * fini_array.size ();
      shdr.sh_link = 0;
      shdr.sh_info = 0;
      shdr.sh_addralign = sizeof (void *);
      shdr.sh_entsize = sizeof (void *);
      shdrs.push_back (shdr);
    }

  /* Build .rela.dynobj.N sections. */
  const int rela_dynobj_section_index = shdrs.size ();
  for (size_t i = 0; i < num_dynobjs; i++)
    {
      Elf64_Shdr shdr;
      shdr.sh_name = shstrtab.add (".rela" + dynobjs[i].name);
      shdr.sh_type = SHT_RELA;
      shdr.sh_flags = SHF_INFO_LINK;
      shdr.sh_addr = 0;
      shdr.sh_offset = 0; /* will be filled later */
      shdr.sh_size = sizeof (Elf64_Rela) * dynobj_rela_tabs[i].size ();
      shdr.sh_link = 0; /* will be filled later (to .symtab section) */
      shdr.sh_info = dynobj_section_index + i;
      shdr.sh_addralign = 8;
      shdr.sh_entsize = sizeof (Elf64_Rela);
      shdrs.push_back (shdr);
    }

  /* Build .rela.init section if .init is present. */
  if (!init_array.empty ())
    {
      Elf64_Shdr shdr;
      shdr.sh_name = shstrtab.add (".rela.init_array");
      shdr.sh_type = SHT_RELA;
      shdr.sh_flags = SHF_INFO_LINK;
      shdr.sh_addr = 0;
      shdr.sh_offset = 0; /* will be filled later */
      shdr.sh_size = init_relas.size () * sizeof (Elf64_Rela);
      shdr.sh_link = 0; /* will be filled later (to .symtab section) */
      shdr.sh_info = init_section_index;
      shdr.sh_addralign = 8;
      shdr.sh_entsize = sizeof (Elf64_Rela);
      shdrs.push_back (shdr);
    }

  /* Build .rela.fini section if .fini is present. */
  if (!fini_array.empty ())
    {
      Elf64_Shdr shdr;
      shdr.sh_name = shstrtab.add (".rela.fini_array");
      shdr.sh_type = SHT_RELA;
      shdr.sh_flags = SHF_INFO_LINK;
      shdr.sh_addr = 0;
      shdr.sh_offset = 0; /* will be filled later */
      shdr.sh_size = fini_relas.size () * sizeof (Elf64_Rela);
      shdr.sh_link = 0; /* will be filled later */
      shdr.sh_info = fini_section_index;
      shdr.sh_addralign = 8;
      shdr.sh_entsize = sizeof (Elf64_Rela);
      shdrs.push_back (shdr);
    }

  /* Build .symtab section */
  const int symtab_idx = shdrs.size ();
  {
    int current_idx = shdrs.size ();
    Elf64_Shdr shdr;
    shdr.sh_name = shstrtab.add (".symtab");
    shdr.sh_type = SHT_SYMTAB;
    shdr.sh_flags = 0;
    shdr.sh_addr = 0;
    shdr.sh_offset = 0; /* will be filled later */
    shdr.sh_size = (symtab.size ()) * sizeof (Elf64_Sym);
    shdr.sh_link = current_idx + 1; /* .strtab section */
    int local_sym_idx
        = dynobj_symbols_start_idx; /* index of first non-local symbol */
    int end_search = (int)symtab.size ();
    for (; local_sym_idx < end_search; local_sym_idx++)
      {
        if (ELF64_ST_BIND (symtab[local_sym_idx].st_info) != STB_LOCAL)
          {
            break;
          }
      }
    shdr.sh_info = local_sym_idx; /* index of first non-local symbol */
    shdr.sh_addralign = 8;
    shdr.sh_entsize = sizeof (Elf64_Sym);
    shdrs.push_back (shdr);
  }

  /* Build .strtab section */
  const int strtab_idx = shdrs.size ();
  {
    Elf64_Shdr shdr;
    shdr.sh_name = shstrtab.add (".strtab");
    shdr.sh_type = SHT_STRTAB;
    shdr.sh_flags = 0;
    shdr.sh_addr = 0;
    shdr.sh_offset = 0; /* will be filled later */
    shdr.sh_size = strtab.size ();
    shdr.sh_link = 0;
    shdr.sh_info = 0;
    shdr.sh_addralign = 1;
    shdr.sh_entsize = 0;
    shdrs.push_back (shdr);
  }

  /* Build .shstrtab section */
  const int shstrtab_idx = shdrs.size ();
  {
    Elf64_Shdr shdr;
    shdr.sh_name = shstrtab.add (".shstrtab");
    shdr.sh_type = SHT_STRTAB;
    shdr.sh_flags = 0;
    shdr.sh_addr = 0;
    shdr.sh_offset = 0; /* will be filled later */
    shdr.sh_size = shstrtab.size ();
    shdr.sh_link = 0;
    shdr.sh_info = 0;
    shdr.sh_addralign = 1;
    shdr.sh_entsize = 0;
    shdrs.push_back (shdr);
  }

  /**
   * ELF file format (relocable file):
   * {ELF Header} {Section headers} {section data}
   */
  off_t offset = sizeof (Elf64_Ehdr) + shdrs.size () * sizeof (Elf64_Shdr);
  auto align_offset = [] (off_t offset, size_t align) {
    if (align == 0)
      {
        align = 1;
      }
    return (offset + align - 1) & ~(align - 1);
  };

  int fd = open (opath, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  if (fd < 0)
    {
      die ("failed to open output file\n");
    }
  std::unique_ptr<int, decltype (&defer_close)> _output_fd_guard (
      &fd, &defer_close);
  auto xfseek = [fd] (off_t offset) {
    if (lseek (fd, offset, SEEK_SET) < 0)
      {
        die ("failed to seek output file\n");
      }
  };

  auto xwrite_section = [&offset, fd, &align_offset,
                         &xfseek] (const void *data, Elf64_Shdr &shdr) {
    auto align = shdr.sh_addralign;
    offset = align_offset (offset, align);
    shdr.sh_offset = offset;
    auto size = shdr.sh_size;
    xfseek (offset);
    if (write (fd, data, size) != (ssize_t)size)
      {
        die ("failed to write output file\n");
      }
    offset += size;
  };

  /* .dynobj.N */
  int next_sect = dynobj_section_index;
  for (size_t i = 0; i < num_dynobjs; i++)
    {
      xwrite_section (dynobjs[i].data, shdrs[next_sect]);
      next_sect += 1;
    }
  /* .init_array */
  if (!init_array.empty ())
    {
      std::vector<unsigned char> dat (init_array.size () * sizeof (void *),
                                      (unsigned char)0x0);
      xwrite_section (dat.data (), shdrs[next_sect]);
      next_sect += 1;
    }
  /* .fini_array */
  if (!fini_array.empty ())
    {
      std::vector<unsigned char> dat (fini_array.size () * sizeof (void *),
                                      (unsigned char)0x0);
      xwrite_section (dat.data (), shdrs[next_sect]);
      next_sect += 1;
    }
  /* .rela.dynobj.N */
  for (size_t i = 0; i < num_dynobjs; i++)
    {
      shdrs[next_sect].sh_link = symtab_idx;
      xwrite_section (dynobj_rela_tabs[i].data (), shdrs[next_sect]);
      next_sect += 1;
    }
  /* .rela.init_array */
  if (!init_array.empty ())
    {
      shdrs[next_sect].sh_link = symtab_idx;
      xwrite_section (init_relas.data (), shdrs[next_sect]);
      next_sect += 1;
    }
  /* .rela.fini_array */
  if (!fini_array.empty ())
    {
      shdrs[next_sect].sh_link = symtab_idx;
      xwrite_section (fini_relas.data (), shdrs[next_sect]);
      next_sect += 1;
    }
  /* .symtab */
  xwrite_section (symtab.data (), shdrs[next_sect]);
  next_sect += 1;
  /* .strtab */
  xwrite_section (strtab.data ().data (), shdrs[next_sect]);
  next_sect += 1;
  /* .shstrtab */
  xwrite_section (shstrtab.data ().data (), shdrs[shstrtab_idx]);

  /* Dump section table. */
  {
    xfseek (sizeof (Elf64_Ehdr));
    ssize_t wb = sizeof (Elf64_Shdr) * shdrs.size ();
    if (write (fd, shdrs.data (), wb) != wb)
      {
        die ("failed to write section table\n");
      }
  }

  Elf64_Ehdr ehdr;
  memset (&ehdr, 0, sizeof (ehdr));
  ehdr.e_ident[EI_MAG0] = ELFMAG0;
  ehdr.e_ident[EI_MAG1] = ELFMAG1;
  ehdr.e_ident[EI_MAG2] = ELFMAG2;
  ehdr.e_ident[EI_MAG3] = ELFMAG3;
  ehdr.e_ident[EI_CLASS] = ELFCLASS64;
  ehdr.e_ident[EI_DATA] = ELFDATA2LSB;
  ehdr.e_ident[EI_VERSION] = EV_CURRENT;
  ehdr.e_type = ET_REL;
  ehdr.e_machine = EM_X86_64;
  ehdr.e_version = EV_CURRENT;
  ehdr.e_ehsize = sizeof (Elf64_Ehdr);
  ehdr.e_shoff = sizeof (Elf64_Ehdr);
  ehdr.e_shentsize = sizeof (Elf64_Shdr);
  ehdr.e_shnum = shdrs.size ();
  ehdr.e_shstrndx = shstrtab_idx;
  xfseek (0);
  if (write (fd, &ehdr, sizeof (ehdr)) != sizeof (ehdr))
    {
      die ("failed to write ELF header\n");
    }
}

} /* (anonymous namespace) */

/**
 * Convert a shared object into a relocatable object.
 *
 * @param in_path    Path of the input shared object.
 * @param out_path   Path of the output relocatable object.
 * @param sect_number First number to use for the generated `.dynobj`
 *                    section names. Sections are named `.dynobj.N`,
 *                    `.dynobj.N+1`, ...
 * @return The next usable `.dynobj` section number, so that successive
 *         calls can keep their section names distinct.
 */
extern "C" unsigned int
convert_so_to_reloc (const char *in_path, const char *out_path,
                     unsigned int sect_number)
{
  int fd = open (in_path, O_RDONLY);
  struct stat stbuf;
  if (fd < 0)
    {
      die ("failed to open input file\n");
    }
  if (fstat (fd, &stbuf) < 0)
    {
      die ("failed to stat input file\n");
    }
  std::unique_ptr<int, decltype (&defer_close)> _input_fd_guard (&fd,
                                                                 &defer_close);

  unsigned char *fdata = new unsigned char[stbuf.st_size];
  if (read (fd, fdata, stbuf.st_size) != stbuf.st_size)
    {
      die ("failed to read input file\n");
    }
  std::unique_ptr<unsigned char[]> _fdata_guard (fdata);

  const Elf64_Ehdr *ehdr = (const Elf64_Ehdr *)fdata;
  if (ehdr->e_type != ET_DYN)
    {
      die ("input file is not a shared object\n");
    }

  const Elf64_Phdr *phdrs = (const Elf64_Phdr *)(fdata + ehdr->e_phoff);
  Elf64_Addr vaddr_max = 0;
  Elf64_Addr vaddr_min = ~0;
  Elf64_Addr vaddr_align = 0x1000; /* hard-code for now. */
  for (int i = 0; i < ehdr->e_phnum; i++)
    {
      const Elf64_Phdr *phdr = &phdrs[i];
      if (phdr->p_type == PT_LOAD)
        {
          vaddr_min = std::min (vaddr_min, phdr->p_vaddr);
          vaddr_max = std::max (vaddr_max, phdr->p_vaddr + phdr->p_memsz);
        }
    }

  assert (vaddr_min == 0);

  /**
   * Create the contiguous image of all loadable segments.
   */
  unsigned char *load_image = new unsigned char[vaddr_max - vaddr_min];
  std::unique_ptr<unsigned char[]> _load_image_guard (load_image);
  memset (load_image, 0, vaddr_max - vaddr_min);
  for (int i = 0; i < ehdr->e_phnum; i++)
    {
      const Elf64_Phdr *phdr = &phdrs[i];
      if (phdr->p_type == PT_LOAD)
        {
          memcpy (load_image + phdr->p_vaddr - vaddr_min,
                  fdata + phdr->p_offset, phdr->p_filesz);
        }
    }

  /**
   * Group loadable segments by writability so that each resulting
   * `.dynobj.N` section is either writable or executable, never both.
   */
  struct LoadRange
  {
    Elf64_Addr start;
    Elf64_Addr end;
    bool writable;
  };
  std::vector<LoadRange> ranges;
  for (int i = 0; i < ehdr->e_phnum; i++)
    {
      const Elf64_Phdr *phdr = &phdrs[i];
      if (phdr->p_type != PT_LOAD)
        {
          continue;
        }
      LoadRange range;
      range.start = phdr->p_vaddr & ~(vaddr_align - 1);
      range.start = std::max (range.start, vaddr_min);
      range.end = phdr->p_vaddr + phdr->p_memsz;
      range.writable = (phdr->p_flags & PF_W) != 0;
      ranges.push_back (range);
    }
  std::sort (ranges.begin (), ranges.end (),
             [] (const LoadRange &a, const LoadRange &b) {
               return a.start < b.start;
             });

  std::vector<DynobjInput> dynobjs;
  for (const LoadRange &range : ranges)
    {
      if (!dynobjs.empty () && dynobjs.back ().writable == range.writable)
        {
          Elf64_Addr cur_end = dynobjs.back ().vaddr + dynobjs.back ().size;
          if (range.end > cur_end)
            {
              dynobjs.back ().size = range.end - dynobjs.back ().vaddr;
            }
          continue;
        }
      DynobjInput dynobj;
      dynobj.writable = range.writable;
      dynobj.data = nullptr;
      dynobj.size = range.end - range.start;
      dynobj.vaddr = range.start;
      dynobjs.push_back (dynobj);
    }
  for (size_t i = 1; i < dynobjs.size (); i++)
    {
      auto &prev = dynobjs[i - 1];
      const auto prev_end = prev.vaddr + prev.size;
      const auto cur_start = dynobjs[i].vaddr;
      assert (prev_end <= cur_start);
      assert (cur_start % vaddr_align == 0);
      prev.size = cur_start - prev.vaddr; /* shrink to fit */
    }
  for (size_t i = 0; i < dynobjs.size (); i++)
    {
      char name[64];
      snprintf (name, sizeof (name), ".dynobj.%u", sect_number + (unsigned)i);
      dynobjs[i].name = name;
      dynobjs[i].data = load_image + (dynobjs[i].vaddr - vaddr_min);
    }
  const unsigned int next_section_number
      = sect_number + (unsigned int)dynobjs.size ();

  const Elf64_Shdr *shdrs = (const Elf64_Shdr *)(fdata + ehdr->e_shoff);
  int shnum = ehdr->e_shnum;
  std::vector<Sym> syms;
  std::unordered_map<Elf64_Word, int> symtab_index_map;
  std::vector<Rela> relas;
#define contains_symbol_table(sh_ty)                                          \
  ((sh_ty) == SHT_SYMTAB || (sh_ty) == SHT_DYNSYM)

#define contains_rela_table(sh_ty) ((sh_ty) == SHT_RELA)
  for (int i = 0; i < shnum; i++)
    {
      const Elf64_Shdr *shdr = &shdrs[i];
      const Elf64_Shdr *linked = &shdrs[shdr->sh_link];
      if (!contains_symbol_table (shdr->sh_type))
        {
          continue;
        }
      assert (shdr->sh_entsize == sizeof (Elf64_Sym));
      assert (shdr->sh_size % sizeof (Elf64_Sym) == 0);
      const Elf64_Sym *symtab = (Elf64_Sym *)(fdata + shdr->sh_offset);
      const int num_syms = shdr->sh_size / sizeof (Elf64_Sym);

      symtab_index_map[(Elf64_Word)i] = syms.size ();
      assert (symtab[0].st_name == 0);
      for (int j = 1; j < num_syms; j++)
        {
          const Elf64_Sym *sym = &symtab[j];
          Sym s;
          s.name = (const char *)(fdata + linked->sh_offset + sym->st_name);
          s.value = sym->st_value;
          s.size = sym->st_size;
          s.info = sym->st_info;
          s.other = sym->st_other;
          s.shndx_is_udf = (unsigned char)(sym->st_shndx == 0);
          syms.push_back (s);
        }
    }
  for (int i = 0; i < shnum; i++)
    {
      const Elf64_Shdr *shdr = &shdrs[i];
      const int linked_idx = shdr->sh_link;
      if (!contains_rela_table (shdr->sh_type))
        {
          continue;
        }
      auto map_iter = symtab_index_map.find (linked_idx);
      assert (map_iter != symtab_index_map.end ());
      assert (shdr->sh_entsize == sizeof (Elf64_Rela));
      assert (shdr->sh_size % sizeof (Elf64_Rela) == 0);
      const Elf64_Rela *relatab = (Elf64_Rela *)(fdata + shdr->sh_offset);
      const int num_relas = shdr->sh_size / sizeof (Elf64_Rela);
      for (int j = 0; j < num_relas; j++)
        {
          const Elf64_Rela *rela = &relatab[j];
          Rela r;
          auto r_sym = ELF64_R_SYM (rela->r_info);
          r.sym = r_sym == 0 ? nullptr /* No associated symbol */
                             : &syms[map_iter->second + r_sym - 1];
          r.offset = rela->r_offset;
          r.type = ELF64_R_TYPE (rela->r_info);
          r.addend = rela->r_addend;
          relas.push_back (r);
        }
    }
  /* Frees symtab map. */
  symtab_index_map.clear ();

  /**
   * Find address of .init and .fini sections
   */
  const char *shstrtab_start
      = (const char *)(fdata + shdrs[ehdr->e_shstrndx].sh_offset);
  std::vector<Elf64_Addr> init_array;
  std::vector<Elf64_Addr> fini_array;
  auto build_addr_array
      = [fdata, vaddr_min, vaddr_max] (const Elf64_Shdr &shdr,
                                       std::vector<Elf64_Addr> &dest) {
          const Elf64_Addr *array_start
              = (const Elf64_Addr *)(fdata + shdr.sh_offset);
          const Elf64_Addr *array_end
              = array_start + (shdr.sh_size / sizeof (Elf64_Addr));
          // dest.clear ();
          assert (dest.empty ()); /* Possibly duplicate section. */
          while (array_start < array_end)
            {
              const auto entr = *array_start;
              assert (entr >= vaddr_min && entr < vaddr_max);
              dest.push_back (entr);
              array_start++;
            }
        };
  for (int i = 0; i < shnum; i++)
    {
      const Elf64_Shdr *shdr = &shdrs[i];
      const char *name = shstrtab_start + shdr->sh_name;
      if (strcmp (name, ".init_array") == 0)
        {
          build_addr_array (*shdr, init_array);
        }
      else if (strcmp (name, ".fini_array") == 0)
        {
          build_addr_array (*shdr, fini_array);
        }
    }

  partition_sym_and_rela (syms, relas, SymIsLocalBind ());
  RelocableFileBuilder builder (std::move (dynobjs));
  builder.syms = std::move (syms);
  builder.relas = std::move (relas);
  builder.init_array = std::move (init_array);
  builder.fini_array = std::move (fini_array);
  builder.dump (out_path);

  return next_section_number;
}

int
main (int argc, char **argv)
{
  if (argc < 3)
    {
      die ("usage: convert <input shared object> <output object> "
           "[section-number]\n");
    }

  const char *input = argv[1];
  const char *output = argv[2];
  unsigned int sect_number = 1;
  if (argc >= 4)
    {
      char *end = nullptr;
      unsigned long parsed = strtoul (argv[3], &end, 0);
      if (end == argv[3] || *end != '\0' || parsed > 0xfffful)
        {
          die ("invalid section number\n");
        }
      sect_number = (unsigned int)parsed;
    }

  convert_so_to_reloc (input, output, sect_number);

  return 0;
}
