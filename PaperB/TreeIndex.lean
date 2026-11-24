module

public import PaperB.Dom
public import PaperB.Machine
public import PaperB.HeavyChild
public import PaperB.StaticHeavyLCA
public import PaperB.StaticHeadSweep
public import PaperB.StaticChildLookup
public import PaperB.PackedStaticLayout
public import PaperB.ActualChildRanges
public import PaperB.DomFromOriginal
public import PaperB.StaticLinearHead
public import PaperB.StaticFromDominators
public import PaperB.StaticTreeReader
public import PaperB.StaticOracleTree

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
`PaperB.TreeIndex` collects the static heavy-path LCA, DFS preorder interval,
head sweep, and ordered child-bucket index over the original dominator tree.
-/
