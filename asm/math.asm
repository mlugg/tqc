%include "runtime.inc"

%macro start_fun 0
	push rbp
	mov rbp, rsp

	mov r8, OBJ_TYPE_FUN
	mov r9, 1
	call alloc
	mov qword [rdi + obj.body + 0], .fn0

	pop rbp
	ret

.fn0:
	push rbp
	mov rbp, rsp

	push r9

	mov r8, OBJ_TYPE_FUN
	mov r9, 2
	call alloc

	pop r9

	mov qword [rdi + obj.body + 0], .fn1
	mov qword [rdi + obj.body + 8], r9

	pop rbp
	ret

.fn1:
	push rbp
	mov rbp, rsp

	push rax
	push rbx

	mov rax, r9
	mov rbx, r8

	; Alloc constr, push to stack
	mov r8, OBJ_TYPE_DATA
	mov r9, 1
	call alloc
	push rdi

	; r8 = first arg
	mov r8, qword [rbx + obj.body + 8]

	; Args in r8, rax
	eval
	mov r8, rdi
	xchg r8, rax
	eval
	mov r8, rdi
	xchg r8, rax
	
	; Now both evaluated! Get values out
	mov r9, qword [r8 + obj.body + 0]   ; First arg
	mov r10, qword [rax + obj.body + 0] ; Second arg
%endmacro
; Code between should take values in r9 and r10 and put result in r11 -
; may clobber rax, rbx
%macro end_fun 0
	pop rdi

	mov qword [rdi + obj.body + 0], r11

	pop rbx
	pop rax

	pop rbp
	ret
%endmacro

section .data

global obj_Data.Nat.#00002b ; +
obj_Data.Nat.#00002b:
	dw FLAG_STATIC
	dw OBJ_TYPE_THUNK_0
	dd 1
	dq mk_add

global obj_Data.Nat.#00002d ; -
obj_Data.Nat.#00002d:
	dw FLAG_STATIC
	dw OBJ_TYPE_THUNK_0
	dd 1
	dq mk_sub

global obj_Data.Nat.#00002a ; *
obj_Data.Nat.#00002a:
	dw FLAG_STATIC
	dw OBJ_TYPE_THUNK_0
	dd 1
	dq mk_mul

global obj_Data.Nat.#00002f ; /
obj_Data.Nat.#00002f:
	dw FLAG_STATIC
	dw OBJ_TYPE_THUNK_0
	dd 1
	dq mk_div

section .text

; Add {{{

mk_add:
	start_fun

	add r9, r10
	mov r11, r9

	end_fun

; }}}

; Sub {{{

mk_sub:
	start_fun

	sub r9, r10
	mov r11, r9

	end_fun

; }}}

; Mul {{{

mk_mul:
	start_fun

	; mul is dumb
	push rdx
	mov rax, r9
	mul r10
	mov r11, rax
	pop rdx

	end_fun

; }}}

; Div {{{

mk_div:
	start_fun

	; div is also dumb
	push rdx
	xor rdx, rdx
	mov rax, r9
	div r10
	mov r11, rax
	pop rdx

	end_fun

; }}}
