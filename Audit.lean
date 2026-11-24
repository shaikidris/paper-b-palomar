module

public import Challenge
public import Solution

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Axiom audit for Theorem 1.1 (`PaperB.two_failure_dag_oracle`) and certified
Paper B upstream milestone roots (Items 2.1, 2.2, 3.1, 3.2, 4.1, and 5.1).
-/

#print axioms PaperB.two_failure_dag_oracle
#print axioms PaperB.two_failure_dag_oracle_v12
#print axioms PaperB.sibling_quotients
#print axioms PaperB.last_exit_test
#print axioms PaperB.proper_loss_forest
#print axioms PaperB.build_proper_loss_forest
#print axioms PaperB.exit_set_transfer
#print axioms PaperB.compressed_exit_summaries
#print axioms PaperB.BytecodeContract.twoFailureOracleBytecode
