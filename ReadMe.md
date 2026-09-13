# Staticizer: Shared Object to Relocable File Converter

**What it does**: takes a shared object as input, copy out
some data to comprise a relocable file for linking.

**Significance**: It may help reduce runtime dependencies.
At link time, we can use a simple linker driver to convert any
shared object inputs into relocable files for linking.

**Assumptions**: x86_64 arch; ELF format.

## Command line

```
convert <input shared object> <output object> [section-number]
```

`section-number` (default `1`) selects the first `.dynobj.N` number, so
that objects converted from several shared objects can be linked
together without section-name collisions. The library entry point
`convert_so_to_reloc(in_path, out_path, sect_number)` returns the next
unused section number.

## Method

1. Split the shared object's loadable (`PT_LOAD`) segments by
writability and copy each group into its own section named `.dynobj.N`
(starting from `section-number`). A group is marked either

   - `AX` (`SHF_ALLOC | SHF_EXECINSTR`) when none of its segments is
     writable, or
   - `AW` (`SHF_ALLOC | SHF_WRITE`) when it is writable.

   Every section is therefore either readable/executable or
   readable/writable, never `WX`. Section starts are page-aligned, and
   each section is sized to reach the next section's start so that the
   `.dynobj.N` sections tile the original address range without gaps,
   preserving the relative virtual addresses of the original image.

2. Read the shared object's relocation sections (`SHT_RELA`, i.e.
`.rela.dyn` and `.rela.plt`) to synthesize the relocation items of the
resulting object file. Since the loadable image is split across several
sections, one relocation section `.rela.dynobj.N` is emitted for each
`.dynobj.N`. Both `Elf64_Rela::r_offset` and `Elf64_Sym::st_value` are
made relative to the beginning of the section they belong to.

3. Construct an `.init_array` section to handle dynamic library initialization.

This section contains only zero-bytes; we rely on the linker to fill it
with address(es) of initialization function(s). For each entry in the shared
object's init\_array, we create a unique symbol using the entry as its value,
and create a relocation item instructing the linker to write the entry's
runtime address into the object file's init\_array.

4. Apply the same rule (in step 3) for `.fini` section.
The resulting relocable file contains `.dynobj.N`, `.init_array`,
`.fini_array`, `.rela.init_array`, `.rela.fini_array`,
`.rela.dynobj.N`, etc.

5. Lastly, edit the linker script so that each `.dynobj.N` keeps its own
permissions:

```diff
+   /* Keep the executable and writable load images separate. */
+   .dynobj.1 : { KEEP (*(.dynobj.1)); }
+   .dynobj.2 : { KEEP (*(.dynobj.2)); }
  _end = .; PROVIDE (end = .);
  . = DATA_SEGMENT_END (.);
```

The current script hard-codes the two stanzas produced for a typical
shared object (one executable group, one writable group), which matches
the default `section-number` of `1`.
