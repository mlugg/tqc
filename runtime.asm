; CALLING CONVENTION
; rax: argument and return val for function bodies
; rbx: function object for function bodies
; rcx: thing to be evaluated for eval
; rax - rdx are scratch registers

; CURRENT EXCEPTION: alloc will not clobber rax/rbx/rdx (but may clobber
; rcx) (Should I remove that special case? It might be a good idea to
; keep tbh; most allocations will be super trivial so won't need the
; other registers, and allocation happens enough that not unneccesarily
; copying the registers a bunch is probably a good plan. on the other
; hand, having possible things in registers makes gc a tiny bit more
; annoying. Leaning towards removing the exception just for consistency)

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
