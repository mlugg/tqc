; CALLING CONVENTION
;   r8-r15, rsi, rdi are scratch registers
;   rax-rdx are preserved
;
;   Arguments passed in r8-r15
;   Return values in rdi
;
;   Preserved registers must only contain object pointers (or NULL)
;   whenever a function is called! This is so that object references can
;   be accurately tracked by the GC.

; For function entry code:
;   r8: function argument
;   r9: function object when calling functions
;   Returns function return value (may be a thunk!)

; For eval:
;   r8: object to eval
;   Returns pointer to evaluated object behind any indirections

; eval takes an object, evaluates to WHNF, and returns the address of
; the object behind any indirections

; alloc takes a closure type in r12, a body size (in words) in r13, and
; returns a pointer to the allocated object in rdx. It automatically
; fills the allocated object's header.

; When adding an object type, make sure to add an entry to the
; eval_table in runtime.asm!
%define OBJ_TYPE_FUN 0
%define OBJ_TYPE_DATA 1
%define OBJ_TYPE_THUNK 2
%define OBJ_TYPE_IND 3
%define OBJ_TYPE_GLOBL 4 ; global unevaluated objects
%define OBJ_TYPE_GLOBL_IND 5 ; distinct from OBJ_TYPE_IND for GC reasons

; Trivial macro for evaluating the value in r8. Clobbers all scratch
; registers.
%macro eval 0
  mov r9d, dword [r8 + obj.type]
  call qword [eval_table + r9d*8]
%endmacro

; NASM structure defining objects
struc obj
  .type: resd 1
  .size: resd 1
  .hdr_size:
  .body:
endstruc
