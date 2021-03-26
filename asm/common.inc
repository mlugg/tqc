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
;
; For function entry code:
;   r8: function object
;   r9: function argument
;   Returns function return value (may be a thunk!)
;
; For eval:
;   r8: object to eval
;   Returns pointer to evaluated object behind any indirections
;
; eval takes an object, evaluates to WHNF, and returns the address of
; the object behind any indirections
;
; alloc takes a closure type and body size (in 64-bit words) as its
; arguments. It automatically fills the closure type and body length
; fields in the object header.
;
; When adding an object type, make sure to add an entry to the
; eval_table in runtime.asm!

%define FLAG_STATIC 1

%define OBJ_TYPE_FUN 0      ; Function
%define OBJ_TYPE_DATA 1     ; Data constructor
%define OBJ_TYPE_THUNK_0 2  ; Nullary thunk
%define OBJ_TYPE_THUNK_1 3  ; Single-argument thunk
%define OBJ_TYPE_IND 4      ; Indirection

; Trivial macro for evaluating the value in r8. Clobbers all scratch
; registers.
%macro eval 0
	movzx r9, word [r8 + obj.type]
	call qword [eval_table + r9*8]
%endmacro

; NASM structure defining objects
struc obj
	.flags: resw 1
	.type: resw 1
	.size: resd 1
	.hdr_size:
	.body:
endstruc
