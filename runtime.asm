; CALLING CONVENTION
; rax: argument
; rbx: function object when calling functions
; rcx: return val
; rax - rdx are scratch registers

; eval takes an object, evaluates to WHNF, and returns the address of
; the object behind any indirections

; alloc does not follow calling convention; it takes a size in rcx,
; returns in rdx, and clobbers only rcx/rdx. This is because for a
; bump-pointer allocator, most allocations are trivial so don't
; need the extra registers; as allocations are incredibly common,
; avoiding the extra push/pop ops is probably good.

%define OBJ_TYPE_FUN 0
%define OBJ_TYPE_DATA 1
%define OBJ_TYPE_THUNK 2
%define OBJ_TYPE_IND 3

struc obj
  .type: resd 1
  .size: resd 1
  .eval: resq 1
  .hdr_size:
  .body:
endstruc

section .text

; eval code for indirections
global eval_ind
eval_ind:
  ; get the object being pointed to
  mov rcx, [rax + obj.body + 0]
  mov rax, rcx

  ; enter the pointed-to object
  ; note tail-call-opt type thing; only thing on stack is return addr,
  ; so no need to call and then return, we can just jump straight to
  ; eval
  jmp [rax + obj.eval]

; eval code for thunks
global eval_thunk
eval_thunk:
  push rbp
  mov rbp, rsp

  ; get the function
  mov rbx, [rax + obj.body + 0]

  ; make sure the function is evaluated
  push rax
  mov rax, rbx
  call [rax + obj.eval]
  pop rax

  ; rcx now contains the "real" function pointer

  mov rbx, rcx

  ; get the argument
  mov rcx, [rax + obj.body + 8]

  push rax

  ; run the function
  mov rax, rcx
  call [rbx + obj.body + 0] ; function entry code
  ; rcx now contains return val
  ; first, eval it in case the function returned another thunk
  mov rax, rcx
  call [rax + obj.eval]
  ; rcx now contains evaluated return val

  pop rax


  ; replace the object with an indirection
  mov dword [rax + obj.type], OBJ_TYPE_IND
  mov dword [rax + obj.eval], eval_ind
  mov [rax + obj.body + 0], rcx

  ; real object ptr already in rcx

  pop rbp
  ret

; eval code for data constructors and functions
global eval_data
global eval_fun
eval_data:
eval_fun:
  ; already evaluated; nothing to do
  mov rcx, rax
  ret

extern asmalloc
; XXX temporary alloc wrapper
global alloc
alloc:
  push rax
  push rbx
  mov rdi, rcx
  call asmalloc
  mov rdx, rax
  pop rbx
  pop rax
  ret
