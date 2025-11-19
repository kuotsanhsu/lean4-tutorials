/-!

- https://docs.riscv.org/reference/isa/unpriv/intro.html
- [IEEE Std 754™-2019](https://doi.org/10.1109/IEEESTD.2019.8766229)

A component is termed a *core* if it contains an independent instruction fetch unit. A RISC-V-compatible core might support multiple RISC-V-compatible hardware threads, or *harts*, through multithreading.

A RISC-V execution environment interface (EEI) defines the initial state of the program, the number and type of harts in the environment including the privilege modes supported by the harts, the accessibility and attributes of memory and I/O regions, the behavior of all legal instructions executed on each hart (i.e., the ISA is one component of the EEI), and the handling of any interrupts or exceptions raised during execution including environment calls. Examples of EEIs include the Linux application binary interface (ABI), or the RISC-V supervisor binary interface (SBI).

A RISC-V hart has a single byte-addressable address space of `2 ^ XLEN` bytes for all memory accesses. A *word* of memory is defined as 32 bits (4 bytes). Correspondingly, a *halfword* is 16 bits (2 bytes), a *doubleword* is 64 bits (8 bytes), and a *quadword* is 128 bits (16 bytes). The memory address space is circular, so that the byte at address `2 ^ XLEN - 1` is adjacent to the byte at address zero. Accordingly, memory address computations done by the hardware ignore overflow and instead wrap around modulo `2 ^ XLEN`.

-/

#check BitVec
#check ByteArray

namespace riscv

abbrev Byte := UInt8
abbrev Halfword := UInt16
abbrev Word := UInt32
abbrev Doubleword := UInt64
structure Quadword where
  ofBitVec ::
  toBitVec : BitVec 128
