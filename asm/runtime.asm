%include "common.inc"

section .data

global eval_table
eval_table:
  dq eval_noop    ; OBJ_TYPE_FUN
  dq eval_noop    ; OBJ_TYPE_DATA
  dq eval_thunk_0 ; OBJ_TYPE_THUNK_0
  dq eval_thunk_1 ; OBJ_TYPE_THUNK_1
  dq eval_ind     ; OBJ_TYPE_IND

section .text

; Evalulation code for data constructors and functions
eval_noop:
  ; Already evaluated; nothing to do
  mov rdi, r8
  ret

; Evaluation code for nullary thunks
eval_thunk_0:
  push rbp
  mov rbp, rsp

  push r8
  call qword [r8 + obj.body + 0]
  pop r8

  ; rdi contains the resulting object
  ; Replace thunk with an indirection
  mov word [r8 + obj.type], OBJ_TYPE_IND
  mov qword [r8 + obj.body + 0], rdi

  pop rbp
  ret

; Evaluation code for single-arg thunks
eval_thunk_1:
  push rbp
  mov rbp, rsp

  ; r9 = function object
  mov r9, qword [r8 + obj.body + 0]

  ; Ensure function object is evaluated
  push r8 ; Push thunk ptr
    mov r8, r9
    eval
  pop r10 ; Pop thunk ptr

  ; rdi now contains the "real" function pointer

  ; r9 = arg object
  mov r9, qword [r10 + obj.body + 8]

  push r10 ; Push thunk ptr
    ; Function pointer needs to be first argument
    mov r8, rdi
    ; Call function entry code
    call qword [r8 + obj.body + 0]
    ; rdi now contains return val
    ; First, eval it in case the function returned another thunk
    mov r8, rdi
    eval
    ; rdi now contains evaluated return val
  pop r8 ; Pop thunk ptr

  ; Replace the thunk with an indirection
  mov word [r8 + obj.type], OBJ_TYPE_IND
  mov qword [r8 + obj.body + 0], rdi

  ; Final object ptr already in rdi

  pop rbp
  ret

; Evaluation code for indirections
eval_ind:
  ; Get the object being pointed to
  mov r9, qword [r8 + obj.body + 0]
  mov r8, r9

  ; Enter the pointed-to object. Note tail-call optimisation; only thing
  ; on stack is return addr, so no need to call and then return, we can
  ; just jump straight to eval
  movzx r9, word [r8 + obj.type]
  jmp qword [eval_table + r9*8]

extern asmalloc

; XXX temporary alloc wrapper
; see common.inc for an explanation of some stuff here
global alloc
alloc:
  push rax
  push rcx
  push rdx

  ; XXX test to see how much allocation there is
  mov rax, qword [alloc_count]
  add rax, rcx
  mov qword [alloc_count], rax
  ; XXX

  mov rdi, r9
  shl rdi, 3
  add rdi, obj.hdr_size

  push r8
  push r9

  call asmalloc

  pop r9
  pop r8

  mov rdi, rax

  mov word [rdi + obj.type], r8w
  mov dword [rdi + obj.size], r9d

  pop rdx
  pop rcx
  pop rax
  ret

section .data

alloc_count: dq 0
