# Staticizer: Shared Object to Relocable File Converter

**What it does**: takes a shared object as input, copy out
some data to comprise a relocable file for linking.

**Significance**: It may help reduce runtime dependencie. 
At link time, we can use a simple linker driver to convert any
shared object inputs into relocable files for linking.

**Assumptions**: x86_64 arch; ELF format.

## Method

1. Construct a new section named `.dynobj` which contains loadable
bytes of a shared object. Mark this section `AWX` (alloc, write, execute).

2. Read the shared object's dynamic relocation sections (type `DYNSYM`)
to synthesize the relocation items of resulting object file.

3. Construct an `.init_array` section to handle dynamic library initialization.

This section contains only zero-bytes; we rely on the linker to fill it
with address(es) of initialization function(s). For each entry in the shared
object's init\_array, we create a unique symbol using the entry as its value,
and create a relocation item instructing the linker to write the entry's
runtime address into the object file's init\_array.

4. Apply the same rule (in step 3) for `.fini` section.
The resulting relocable file contains `.dynobj`, `.init_array`, `.fini_array`, `.rela.init_array`,
`.rela.fini_array`, `.rela.dynobj`, etc.

5. Lastly, edit the linker script to  handle our `.dynobj` section(s):

```diff
+   /* Include loadable segment of shared object as a whole. */
+   .dynobj   : {  KEEP (*(.dynobj)); }
  _end = .; PROVIDE (end = .);
  . = DATA_SEGMENT_END (.);
```
