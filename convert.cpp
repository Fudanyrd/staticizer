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

static const char _dynobj_section_name[] = ".dynobj";

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

struct RelocableFileBuilder
{
  std::vector<Sym> syms;
  std::vector<Rela> relas;
  unsigned char *dynobj_section_data;
  size_t dynobj_section_size;
  std::vector<Elf64_Addr> init_array;
  std::vector<Elf64_Addr> fini_array;

  // RelocableFileBuilder () : strtab (), shstrtab (), syms (), relas () {}
  RelocableFileBuilder (unsigned char *dynobj_section_data,
                        size_t dynobj_section_size)
      : syms (), relas (), dynobj_section_data (dynobj_section_data),
        dynobj_section_size (dynobj_section_size)
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

  StringTable strtab;
  std::vector<Elf64_Sym> symtab;
  symtab.push_back (NULL_SYM);
  std::vector<Elf64_Rela> dynobj_rela_tab;
  const int dynobj_section_index = shdrs.size (); /* which is 1 */
  /* Symbol for init and fini function. */
  std::vector<Elf64_Rela> init_relas; /* .rela.init_array */
  std::vector<Elf64_Rela> fini_relas; /* .rela.init_array */
  {
    auto build_sym_and_rela_for_entr
        = [dynobj_section_index] (
              std::vector<Elf64_Rela> &relas, std::vector<Elf64_Sym> &symtab,
              StringTable &strtab, const char *name_prefix, Elf64_Addr entry) {
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
            s.st_shndx = dynobj_section_index;
            s.st_value = entry;
            s.st_size = 0; /* UNKNOWN */

            relas.push_back (rela);
            symtab.push_back (s);
          };

    for (Elf64_Addr entry : init_array)
      {
        build_sym_and_rela_for_entr (init_relas, symtab, strtab, "_init",
                                     entry);
      }
    for (Elf64_Addr entry : fini_array)
      {
        build_sym_and_rela_for_entr (fini_relas, symtab, strtab, "_fini",
                                     entry);
      }
    assert (fini_relas.size () == fini_array.size ());
    assert (init_relas.size () == init_array.size ());
  }

  const int dynobj_symbols_start_idx = symtab.size ();
  for (const Sym &sym : syms)
    {
      auto name = strtab.add (sym.name);
      Elf64_Sym s;
      s.st_name = name;
      s.st_info = sym.info;
      s.st_other = sym.other;
      s.st_shndx = sym.shndx_is_udf ? 0 : dynobj_section_index;
      s.st_value = sym.value;
      s.st_size = sym.size;
      symtab.push_back (s);
    }
  for (const Rela &rela : relas)
    {
      Elf64_Xword sym_idx = 0;
      if (rela.sym)
        {
          sym_idx = rela.sym - syms.data ();
          /* Add offset to the index of the first symbol in .dynobj section. */
          sym_idx += dynobj_symbols_start_idx;
        }
      Elf64_Rela r;
      r.r_offset = rela.offset;
      r.r_info = ELF64_R_INFO (sym_idx, reloc_type_convert (rela.type));
      r.r_addend = rela.addend;
      dynobj_rela_tab.push_back (r);
    }

  /* Build .dynobj section. */
  {
    Elf64_Shdr shdr;
    shdr.sh_name = shstrtab.add (_dynobj_section_name);
    shdr.sh_type = SHT_PROGBITS;
    shdr.sh_flags = SHF_ALLOC | SHF_WRITE | SHF_EXECINSTR;
    shdr.sh_addr = 0;
    shdr.sh_offset = 0; /* will be filled later */
    shdr.sh_size = dynobj_section_size;
    shdr.sh_link = 0;
    shdr.sh_info = 0;
    shdr.sh_addralign = 0x1000;
    shdr.sh_entsize = 0;
    shdrs.push_back (shdr);
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

  /* Build .rela.dynobj section */
  {
    Elf64_Shdr shdr;
    shdr.sh_name = shstrtab.add (".rela.dynobj");
    shdr.sh_type = SHT_RELA;
    shdr.sh_flags = SHF_INFO_LINK;
    shdr.sh_addr = 0;
    shdr.sh_offset = 0; /* will be filled later */
    shdr.sh_size = sizeof (Elf64_Rela) * dynobj_rela_tab.size ();
    shdr.sh_link = 0; /* will be filled later (to .symtab section) */
    shdr.sh_info = dynobj_section_index;
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
      shdr.sh_size = fini_array.size () * sizeof (Elf64_Rela);
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

  /* .dynobj */
  int next_sect = dynobj_section_index;
  xwrite_section (dynobj_section_data, shdrs[next_sect]);
  next_sect += 1;
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
  /* .rela.dynobj */
  shdrs[next_sect].sh_link = symtab_idx;
  xwrite_section (dynobj_rela_tab.data (), shdrs[next_sect]);
  next_sect += 1;
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

int
main (int argc, char **argv)
{
  const char *input = argv[1];
  if (input == nullptr)
    {
      die ("usage: <input shared object>\n");
    }

  int fd = open (input, O_RDONLY);
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
   * Create .dynobj section data.
   */
  unsigned char *dynobj_section_data
      = new unsigned char[vaddr_max - vaddr_min];
  std::unique_ptr<unsigned char[]> _dynobj_section_data_guard (
      dynobj_section_data);
  memset (dynobj_section_data, 0, vaddr_max - vaddr_min);
  for (int i = 0; i < ehdr->e_phnum; i++)
    {
      const Elf64_Phdr *phdr = &phdrs[i];
      if (phdr->p_type == PT_LOAD)
        {
          memcpy (dynobj_section_data + phdr->p_vaddr - vaddr_min,
                  fdata + phdr->p_offset, phdr->p_filesz);
        }
    }

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
  RelocableFileBuilder builder (dynobj_section_data, vaddr_max - vaddr_min);
  builder.syms = std::move (syms);
  builder.relas = std::move (relas);
  builder.init_array = std::move (init_array);
  builder.fini_array = std::move (fini_array);
  builder.dump ("output.o");

  return 0;
}
