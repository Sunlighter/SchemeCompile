<!-- -*- coding: utf-8; fill-column: 118 -*- -->

# SchemeCompiler

This project includes an old Scheme interpreter and an old Scheme compiler, both written in F#.

The compiler produces series of opcodes, which can be formatted to look like C#. This branch represents an attempt to
create a runtime which runs those opcodes.

Both the interpreter and the compiler support proper tail calls; the interpreter also supports call/cc.
