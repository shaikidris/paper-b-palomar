module

public import PaperB.OracleContract
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

/-! Word capacity arithmetic is part of the public oracle model. -/
