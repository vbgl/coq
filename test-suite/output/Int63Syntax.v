Require Import Int63 Cyclic63.

Open Scope int63_scope.
Check 2.
Check 1000000000000000000000000000000000000000.
Check (Int63.add 2 2).
Check (2+2).
Eval vm_compute in 2+2.
Eval vm_compute in 65675757 * 565675998.
Close Scope int63_scope.
