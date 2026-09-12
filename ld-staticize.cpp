// staticize-ld : a front-end to the GNU/LLVM linker that prefers static
// libraries over shared ones, so the resulting binary pulls in fewer
// runtime dependencies.
//
// Build:
//   g++ -std=c++17 -O2 -o staticize-ld staticize-ld.cpp
//
// Usage: replace the linker invocation with this tool. It inspects every
//   -lNAME / shared-object input, and when a static library plus a usable
//   dependency closure can be found it rewrites the command line and execs
//   the real linker.
//
// Environment variables:
// - STATICIZE_LINKER : path or name of the real linker (default: search PATH)
// - STATICIZE_VERBOSE : if set, print the search path and rewritten command
// - STATICIZE_EXTRA_ARG : if set, pass this extra argument to the real linker
//
// The real linker is taken from the STATICIZE_LINKER environment variable
// (a path or a name found on PATH). If unset, a wrapper installed as a
// symlink named like the real linker is resolved by skipping itself, and
// finally a plain "ld" on PATH is used.
//
// Notes / limitations:
//   * Response files (@file) are passed through untouched.
//   * -pie / --pic-executable are dropped (static archives are often not
//     built with -fPIC).
//   * libc, libm and ld.so are never statically resolved (hard-coded).

#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <string>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using std::error_code;
using std::string;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace fs = std::filesystem;

// ---------------------------------------------------------------------------
// Small utilities
// ---------------------------------------------------------------------------

static void
errDie (const string &m)
{
  fprintf (stderr, "staticize-ld: %s\n", m.c_str ());
  exit (1);
}

static bool
startsWith (const string &s, const string &p)
{
  return s.size () >= p.size () && s.compare (0, p.size (), p) == 0;
}

static string
baseName (const string &p)
{
  size_t s = p.find_last_of ('/');
  return s == string::npos ? p : p.substr (s + 1);
}

static string
dirName (const string &p)
{
  size_t s = p.find_last_of ('/');
  if (s == string::npos)
    return "";
  if (s == 0)
    return "/";
  return p.substr (0, s);
}

static bool
fileExists (const string &p)
{
  struct stat st;
  return stat (p.c_str (), &st) == 0 && S_ISREG (st.st_mode);
}

// ---------------------------------------------------------------------------
// Options that consume the next argument, exactly as listed in the spec
// ---------------------------------------------------------------------------

static const char *kValueOpts[] = {
  "-a",
  "--audit",
  "-b",
  "-c",
  "--depaudit",
  "-P",
  "-e",
  "--exclude-libs",
  "--exclude-modules-for-implib",
  "-f",
  "-F",
  "-G",
  "-h",
  "-m",
  "-o",
  "-O",
  "-plugin",
  "-R",
  "-T",
  "-dT",
  "-u",
  "-y",
  "-Y",
  "-z",
  "-assert",
  "--out-implib",
  "--heap",
  "--major-image-version",
  "--major-os-version",
  "--major-subsystem-version",
  "--minor-image-version",
  "--minor-os-version",
  "--output-def",
  "--dll-search-prefix",
  "--stack",
  "--subsystem",
  "--dsbt-size",
  "--dsbt-index",
  "--bank-window",
};

// Single-letter options that take a value. "-oFILE" is equivalent to "-o
// FILE".
static const char *kShortValueLetters = "abcPefFGhmORzTuyY";

static bool
isValueOptExact (const string &a)
{
  for (const char *o : kValueOpts)
    if (a == o)
      return true;
  return false;
}

// "-oFILE": value glued to a short option.
static bool
isValueOptGlued (const string &a)
{
  if (a.size () < 3 || a[0] != '-' || a[1] == '-')
    return false;
  return strchr (kShortValueLetters, a[1]) != nullptr;
}

// ---------------------------------------------------------------------------
// ELF helpers: read DT_NEEDED of a shared object
// ---------------------------------------------------------------------------

static uint16_t
rd16 (const uint8_t *p, bool le)
{
  return le ? (uint16_t)((uint16_t)p[0] | ((uint16_t)p[1] << 8))
            : (uint16_t)(((uint16_t)p[0] << 8) | p[1]);
}
static uint32_t
rd32 (const uint8_t *p, bool le)
{
  if (le)
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16)
           | ((uint32_t)p[3] << 24);
  return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16)
         | ((uint32_t)p[2] << 8) | (uint32_t)p[3];
}
static uint64_t
rd64 (const uint8_t *p, bool le)
{
  uint64_t lo = rd32 (p, le);
  uint64_t hi = rd32 (p + 4, le);
  return le ? (lo | (hi << 32)) : ((lo << 32) | hi);
}

struct ParsedDyn
{
  bool elf = false;      // file looked like an ELF image
  vector<string> needed; // DT_NEEDED strings
};

static bool
readFileBytes (const string &path, vector<uint8_t> &out)
{
  FILE *f = fopen (path.c_str (), "rb");
  if (!f)
    return false;
  if (fseek (f, 0, SEEK_END) != 0)
    {
      fclose (f);
      return false;
    }
  long sz = ftell (f);
  if (fseek (f, 0, SEEK_SET) != 0)
    {
      fclose (f);
      return false;
    }
  if (sz < 0)
    {
      fclose (f);
      return false;
    }
  out.resize ((size_t)sz);
  size_t got = sz ? fread (out.data (), 1, (size_t)sz, f) : 0;
  fclose (f);
  return got == (size_t)sz;
}

static ParsedDyn
parseNeeded (const uint8_t *b, size_t n)
{
  ParsedDyn pd;
  if (n < 18)
    return pd;
  if (!(b[0] == 0x7f && b[1] == 'E' && b[2] == 'L' && b[3] == 'F'))
    return pd;
  pd.elf = true;

  int cls = b[4];      // EI_CLASS
  bool le = b[5] == 1; // EI_DATA

  uint64_t phoff = 0, dynOff = 0, dynSize = 0;
  uint32_t phentsz = 0, phnum = 0;
  if (cls == 2)
    { // ELFCLASS64
      if (n < 64)
        return pd;
      phoff = rd64 (b + 32, le);
      phentsz = rd16 (b + 54, le);
      phnum = rd16 (b + 56, le);
    }
  else if (cls == 1)
    { // ELFCLASS32
      if (n < 52)
        return pd;
      phoff = rd32 (b + 28, le);
      phentsz = rd16 (b + 42, le);
      phnum = rd16 (b + 44, le);
    }
  else
    {
      return pd;
    }
  if (!phoff || !phentsz || !phnum)
    return pd;

  struct Load
  {
    uint64_t vaddr, off, size;
  };
  vector<Load> loads;
  for (uint32_t i = 0; i < phnum; i++)
    {
      size_t base = (size_t)(phoff + (uint64_t)i * phentsz);
      if (base + phentsz > n)
        break;
      uint32_t type;
      uint64_t off, vaddr, size;
      if (cls == 2)
        {
          type = rd32 (b + base + 0, le);
          off = rd64 (b + base + 8, le);
          vaddr = rd64 (b + base + 16, le);
          size = rd64 (b + base + 32, le);
        }
      else
        {
          type = rd32 (b + base + 0, le);
          off = rd32 (b + base + 4, le);
          vaddr = rd32 (b + base + 8, le);
          size = rd32 (b + base + 16, le);
        }
      if (type == 1)
        loads.push_back ({ vaddr, off, size });
      else if (type == 2)
        {
          dynOff = off;
          dynSize = size;
        }
    }
  if (!dynOff || !dynSize)
    return pd;

  auto offOfVaddr = [&] (uint64_t va) -> uint64_t {
    for (const auto &s : loads)
      if (va >= s.vaddr && va < s.vaddr + s.size)
        return s.off + (va - s.vaddr);
    return ~0ull;
  };

  size_t step = cls == 2 ? 16 : 8;
  uint64_t count = dynSize / step;
  uint64_t strtabVA = 0;
  vector<uint64_t> needOffs;
  for (uint64_t j = 0; j < count; j++)
    {
      size_t pos = (size_t)(dynOff + j * step);
      if (pos + step > n)
        break;
      uint64_t tag = cls == 2 ? rd64 (b + pos, le) : rd32 (b + pos, le);
      uint64_t val
          = cls == 2 ? rd64 (b + pos + 8, le) : rd32 (b + pos + 4, le);
      if (tag == 0)
        break; // DT_NULL
      if (tag == 1)
        needOffs.push_back (val); // DT_NEEDED
      else if (tag == 5)
        strtabVA = val; // DT_STRTAB
    }
  if (!strtabVA || needOffs.empty ())
    return pd;

  uint64_t strOff = offOfVaddr (strtabVA);
  if (strOff == ~0ull)
    return pd;

  for (uint64_t o : needOffs)
    {
      uint64_t s = strOff + o;
      if (s >= n)
        continue;
      size_t e = (size_t)s;
      while (e < n && b[e] != 0)
        e++;
      if (e > s)
        pd.needed.emplace_back ((const char *)b + s, e - s);
    }
  return pd;
}

// ---------------------------------------------------------------------------
// Library naming / search
// ---------------------------------------------------------------------------

static const char *kDefaultDirs[] = {
  "/usr/local/lib/x86_64-linux-gnu",
  "/lib/x86_64-linux-gnu",
  "/usr/lib/x86_64-linux-gnu",
  "/usr/lib/x86_64-linux-gnu64",
  "/usr/local/lib64",
  "/lib64",
  "/usr/lib64",
  "/usr/local/lib",
  "/lib",
  "/usr/lib",
  "/usr/x86_64-linux-gnu/lib64",
  "/usr/x86_64-linux-gnu/lib",
};

static vector<string> g_dirs; // -L dirs followed by the hard-coded list
static vector<string> g_out;  // rewritten command line (grows)

// "libfoo.so.1" / "libfoo.so" / "libfoo.a" / "foo" -> library name "foo"
static string
libNameOf (const string &p)
{
  string f = baseName (p);
  size_t k = f.find (".so");
  if (k != string::npos)
    f.erase (k);
  if (startsWith (f, "lib") && f.size () > 3)
    return f.substr (3);
  return f;
}

static bool
isExcludedName (const string &name)
{
  return name == "c" || name == "m";
}

// Excluded NEEDED entries: libc, libm and the dynamic loader.
static bool
isExcludedSoname (const string &soname)
{
  string nm = libNameOf (soname);
  if (isExcludedName (nm))
    return true;
  if (startsWith (soname, "ld-") || startsWith (soname, "ld.so"))
    return true;
  return false;
}

static string
findInDirs (const string &rel, const vector<string> *extra = nullptr)
{
  auto tryDir = [&] (const string &d) -> string {
    string p = d;
    if (!p.empty () && p.back () != '/')
      p += '/';
    p += rel;
    return fileExists (p) ? p : string ();
  };
  if (extra)
    for (const auto &d : *extra)
      {
        string r = tryDir (d);
        if (!r.empty ())
          return r;
      }
  for (const auto &d : g_dirs)
    {
      string r = tryDir (d);
      if (!r.empty ())
        return r;
    }
  return "";
}

static string
findStaticLib (const string &name, const vector<string> *extra = nullptr)
{
  return findInDirs ("lib" + name + ".a", extra);
}

// Search for libNAME.so, falling back to a versioned libNAME.so.* file.
static string
findSharedByName (const string &name)
{
  string r = findInDirs ("lib" + name + ".so");
  if (!r.empty ())
    return r;
  string pref = "lib" + name + ".so";
  vector<string> extra;
  for (const auto &d : g_dirs)
    {
      string best;
      error_code ec;
      if (!fs::is_directory (d, ec))
        continue;
      for (auto it = fs::directory_iterator (d, ec),
                end = fs::directory_iterator ();
           !ec && it != end; it.increment (ec))
        {
          string fn = it->path ().filename ().string ();
          if (startsWith (fn, pref) && fn.size () > pref.size ())
            if (best.empty () || fn > best)
              best = fn;
        }
      if (!best.empty ())
        {
          string p = d;
          if (p.back () != '/')
            p += '/';
          return p + best;
        }
    }
  return "";
}

// For a DT_NEEDED soname, locate the actual file (usually versioned).
static string
findSoname (const string &soname)
{
  string r = findInDirs (soname);
  if (!r.empty ())
    return r;
  return findSharedByName (libNameOf (soname));
}

// ---------------------------------------------------------------------------
// NEEDED cache
// ---------------------------------------------------------------------------

static unordered_map<string, ParsedDyn> g_neededCache;

static const ParsedDyn &
neededOf (const string &path)
{
  auto it = g_neededCache.find (path);
  if (it != g_neededCache.end ())
    return it->second;
  ParsedDyn pd;
  vector<uint8_t> bytes;
  if (readFileBytes (path, bytes) && !bytes.empty ())
    pd = parseNeeded (bytes.data (), bytes.size ());
  return g_neededCache.emplace (path, std::move (pd)).first->second;
}

// Report whether a file is an ELF shared object (ET_DYN).
static bool
isSharedObject (const string &path)
{
  FILE *f = fopen (path.c_str (), "rb");
  if (!f)
    return false;
  uint8_t hdr[20] = { 0 };
  size_t got = fread (hdr, 1, sizeof hdr, f);
  fclose (f);
  if (got < 20)
    return false;
  if (!(hdr[0] == 0x7f && hdr[1] == 'E' && hdr[2] == 'L' && hdr[3] == 'F'))
    return false;
  uint16_t type = rd16 (hdr + 16, hdr[5] == 1);
  return type == 3; // ET_DYN
}

// ---------------------------------------------------------------------------
// Rewriting logic
// ---------------------------------------------------------------------------

static void emitDep (const string &soname, const string &name,
                     unordered_set<string> &visited);

// Expand the DT_NEEDED closure of a located shared object, emitting
// replacements for every dependency that is not excluded.
static void
expandNeeded (const string &soPath, unordered_set<string> &visited)
{
  if (soPath.empty ())
    return;
  const ParsedDyn &pd = neededOf (soPath);
  if (!pd.elf)
    return;
  for (const string &soname : pd.needed)
    {
      if (isExcludedSoname (soname))
        continue;
      string nm = libNameOf (soname);
      if (visited.count (nm))
        continue;
      visited.insert (nm);
      emitDep (soname, nm, visited);
    }
}

static void
emitDep (const string &soname, const string &name,
         unordered_set<string> &visited)
{
  string so = findSoname (soname);
  string a = findStaticLib (name);
  if (!a.empty ())
    {
      g_out.push_back (a);
      expandNeeded (so, visited);
    }
  else if (!so.empty ())
    {
      g_out.push_back (so);
      expandNeeded (so, visited);
    }
  else
    {
      // Last resort: let the real linker perform its own search.
      g_out.push_back ("-l" + name);
    }
}

// Process a root -lNAME. If no static library exists, keep the shared one.
static void
processRootLibrary (const string &name)
{
  if (isExcludedName (name))
    {
      g_out.push_back ("-l" + name);
      return;
    }
  string a = findStaticLib (name);
  if (a.empty ())
    {
      g_out.push_back ("-l" + name);
      return;
    }
  g_out.push_back (a);
  string so = findSharedByName (name);
  unordered_set<string> visited;
  visited.insert (name);
  if (!so.empty ())
    {
      if (!neededOf (so).elf)
        fprintf (stderr,
                 "staticize-ld: note: %s is not an ELF shared object; "
                 "staticized but dependency scan skipped\n",
                 so.c_str ());
      expandNeeded (so, visited);
    }
}

// Process a positional shared-object input path.
static void
processInputFile (const string &path)
{
  string base = baseName (path);
  if (base.find (".so") == string::npos)
    {
      g_out.push_back (path);
      return;
    }
  if (!fileExists (path) || !isSharedObject (path))
    {
      g_out.push_back (path);
      return;
    }
  string nm = libNameOf (path);
  if (isExcludedName (nm))
    {
      g_out.push_back (path);
      return;
    }
  vector<string> extra;
  string dir = dirName (path);
  if (!dir.empty ())
    extra.push_back (dir);
  string a = findStaticLib (nm, &extra);
  if (a.empty ())
    {
      g_out.push_back (path);
      return;
    }
  g_out.push_back (a);
  if (!neededOf (path).elf)
    fprintf (stderr,
             "staticize-ld: note: %s is not an ELF shared object; "
             "staticized but dependency scan skipped\n",
             path.c_str ());
  unordered_set<string> visited;
  visited.insert (nm);
  expandNeeded (path, visited);
}

// One scan pass. First pass (out == nullptr) collects -L dirs so that they are
// known before any rewriting happens; second pass builds the new command line.
static void
scanArgs (const vector<string> &av, vector<string> &userDirs,
          vector<string> *out)
{
  bool afterDD = false;
  size_t i = 0;
  auto push = [&] (const string &s) {
    if (out)
      out->push_back (s);
  };

  while (i < av.size ())
    {
      const string &a = av[i];

      if (!afterDD && a == "--")
        {
          afterDD = true;
          push (a);
          i++;
          continue;
        }

      bool isOpt = !afterDD && !a.empty () && a[0] == '-';

      if (isOpt)
        {
          if (a == "-pie" || a == "--pic-executable")
            {
              i++; // dropped on purpose
              continue;
            }
          if (a == "-l")
            { // "-l NAME"
              if (i + 1 < av.size ())
                {
                  if (out)
                    processRootLibrary (av[i + 1]);
                  i += 2;
                }
              else
                {
                  push (a);
                  i++;
                }
              continue;
            }
          if (startsWith (a, "-l:") || startsWith (a, "-L:"))
            {
              push (a); // exact-name lib/dir, keep as-is
              i++;
              continue;
            }
          if (startsWith (a, "-l"))
            { // "-lNAME"
              if (out)
                processRootLibrary (a.substr (2));
              i++;
              continue;
            }
          if (a == "-L")
            { // "-L DIR"
              if (i + 1 < av.size ())
                {
                  if (!out)
                    userDirs.push_back (av[i + 1]);
                  push (a);
                  push (av[i + 1]);
                  i += 2;
                }
              else
                {
                  push (a);
                  i++;
                }
              continue;
            }
          if (startsWith (a, "-L"))
            { // "-LDIR"
              if (!out)
                userDirs.push_back (a.substr (2));
              push (a);
              i++;
              continue;
            }
          if (isValueOptExact (a))
            { // consume the following value
              push (a);
              if (i + 1 < av.size ())
                {
                  push (av[i + 1]);
                  i += 2;
                }
              else
                {
                  i++;
                }
              continue;
            }
          if (isValueOptGlued (a))
            { // "-oVALUE": value already in token
              push (a);
              i++;
              continue;
            }
          push (a); // any other option, pass through
          i++;
          continue;
        }

      // Positional argument: an input file.
      if (out)
        processInputFile (a);
      i++;
    }
}

// ---------------------------------------------------------------------------
// Locate and exec the real linker
// ---------------------------------------------------------------------------

static string
findOnPath (const string &name, const string &selfPath)
{
  const char *path = getenv ("PATH");
  if (!path)
    return "";
  string saved = path;
  size_t start = 0;
  while (start <= saved.size ())
    {
      size_t end = saved.find (':', start);
      if (end == string::npos)
        end = saved.size ();
      string dir = saved.substr (start, end - start);
      if (dir.empty ())
        dir = ".";
      string cand = dir;
      if (cand.back () != '/')
        cand += '/';
      cand += name;
      if (fileExists (cand) && access (cand.c_str (), X_OK) == 0)
        {
          if (!selfPath.empty ())
            {
              struct stat s1, s2;
              if (stat (cand.c_str (), &s1) == 0
                  && stat (selfPath.c_str (), &s2) == 0
                  && s1.st_dev == s2.st_dev && s1.st_ino == s2.st_ino)
                {
                  // this is ourselves; keep looking
                  start = end + 1;
                  continue;
                }
            }
          return cand;
        }
      if (end == saved.size ())
        break;
      start = end + 1;
    }
  return "";
}

static string
resolveRealLinker (const string &selfPath)
{
  const char *env = getenv ("STATICIZE_LINKER");
  if (env && *env)
    {
      string e = env;
      if (e.find ('/') == string::npos)
        {
          string r = findOnPath (e, selfPath);
          if (!r.empty ())
            return r;
        }
      else if (fileExists (e))
        {
          return e;
        }
      errDie ("STATICIZE_LINKER set but not usable: " + e);
    }

  string ownName = baseName (selfPath);
  if (!ownName.empty ())
    {
      string r = findOnPath (ownName, selfPath);
      if (!r.empty ())
        return r;
    }
  for (const char *c : { "ld", "ld.gold", "ld.lld", "lld" })
    {
      string r = findOnPath (c, selfPath);
      if (!r.empty ())
        return r;
    }
  errDie ("cannot locate the real linker; set STATICIZE_LINKER");
  return "";
}

int
main (int argc, char **argv)
{
  vector<string> av;
  for (int i = 1; i < argc; i++)
    av.push_back (argv[i]);

  vector<string> userDirs;
  scanArgs (av, userDirs, nullptr); // gather -L dirs first

  g_dirs = userDirs;
  for (const char *d : kDefaultDirs)
    g_dirs.push_back (d);

  scanArgs (av, userDirs, &g_out); // rewrite

  if (getenv ("STATICIZE_VERBOSE"))
    {
      fprintf (stderr, "staticize-ld: search path:\n");
      for (const auto &d : g_dirs)
        fprintf (stderr, "  %s\n", d.c_str ());
      fprintf (stderr, "staticize-ld: rewritten command:\n  ");
      for (const auto &t : g_out)
        fprintf (stderr, "%s ", t.c_str ());
      fprintf (stderr, "\n");
    }

  string real = resolveRealLinker (argv[0]);

  vector<const char *> cmd;
  cmd.push_back (real.c_str ());
  /* 
   * Extra arguments passed to actual linker 
   * (at most one; use @file for multiple args). 
   */
  const char *extra_arg = getenv ("STATICIZE_EXTRA_ARG");
  if (extra_arg && *extra_arg)
    {
      cmd.push_back (extra_arg);
    }
  for (const auto &t : g_out)
    cmd.push_back (t.c_str ());
  cmd.push_back (nullptr);

  execv (real.c_str (), const_cast<char *const *> (cmd.data ()));
  errDie (string ("failed to exec ") + real + ": " + strerror (errno));
  return 1;
}
