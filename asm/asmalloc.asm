; Page size = 1 << PGSHF
%define PGSHF 12

struc block
	.size:	resq 1
	.alloc:	resq 1
	.free:	resq 1
	.next:	resq 1
	.sizeof:
endstruc

global asmalloc
section .text
asmalloc:
	push r12
	push r13
	
	; Determine block size
	cmp rdi, 64
	jle .64
	cmp rdi, 1024
	jle .1k

	; Large block
	;; size = (size + sizeof (struct block) - 1) / PAGE + 1
	add rdi, block.sizeof - 1
	shr rdi, PGSHF
	inc rdi
	;; _lg = newblock(size, _lg)
	mov rsi, qword [_lg]
	call _newblock
	mov qword [_lg], rax
	;; return _lg->alloc
	mov rax, qword [rax + block.alloc]
	pop r13
	pop r12
	ret

	; Small blocks
.1k:
	mov r13, 1024
	mov r12, _1k
	jmp .alloc
.64:
	mov r13, 64
	mov r12, _64
.alloc:
	;; if (!*block)
	mov rax, qword [r12]
	and rax, rax
	jnz .allocfree

	;; *block = _newblock(8, NULL)
	mov rdi, 8
	xor rsi, rsi
	call _newblock
	mov qword [r12], rax

.allocfree:
	mov rsi, rax
	; Try to allocate from the free list
	;; if (blk->free)
	mov rax, [rsi + block.free]
	and rax, rax
	jz .checkalloc
	;; blk->free = *blk->free
	mov [rsi + block.free], rax
	;; return mem
	pop r13
	pop r12
	ret

.checkalloc:
	; Check if there is space for a new element
	;; mem = blk->alloc
	mov rax, qword [rsi + block.alloc]
	;; mem2 = mem + block_size
	lea rdi, [rax + r13]
	;; if (mem2 > blk)
	cmp rdi, rsi
	jle .allocalloc
	; No space, make a new block
	;; blk = _newblock(8, blk);
	mov rdi, 8
	call _newblock
	mov rsi, rax
	;; *block = blk
	mov qword [r12], rsi
	;; mem = blk->alloc
	mov rax, qword [rsi + block.alloc]
	;; mem2 = mem + block_size
	lea rdi, [rax + r13]

.allocalloc:
	; Allocate a new element
	;; blk->alloc = mem2
	mov qword [rsi + block.alloc], rdi
	;; return mem
	pop r13
	pop r12
	ret

_newblock:
	; Save args
	push rdi
	push rsi
	
	;; pages = mmap(NULL, n * PAGE, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0)
	;;; offset = 0
	xor r9, r9
	;;; Linux ignores fd when MAP_ANONYMOUS, so don't waste time initializing it
	;;; flags = MAP_PRIVATE|MAP_ANONYMOUS
	mov r10, 0x22
	;;; prot = PROT_READ|PROT_WRITE
	mov rdx, 3
	;;; length = n * PAGE
	shl rdi, PGSHF
	mov rsi, rdi
	;;; addr = NULL
	xor rdi, rdi
	;;; Execute the call
	mov rax, 9 ; SYS_MMAP
	syscall
	mov rdx, rax
	; TODO: handle errors

	; Restore args
	pop rsi
	pop rdi

	; Initialize block
	;; blk = pages + n*PAGE - sizeof (struct block)
	mov rcx, rdi
	shl rcx, PGSHF
	lea rax, [rdx + rcx - 32]
	;; blk->size = n
	mov qword [rax + block.size], rdi
	;; blk->alloc = pages
	mov qword [rax + block.alloc], rdx
	;; blk->next = next
	mov qword [rax + block.next], rsi

	;; return blk
	ret

section .bss
_64:	resq 1
_1k:	resq 1
_lg:	resq 1
