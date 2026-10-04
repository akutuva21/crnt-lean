import CRNT.Dynamics.UpperRegionAdjudication

/-!
# Pins for the Hole-A fork adjudication

`CRNT/Dynamics/UpperRegionAdjudication.lean` decides the contest between `form-barrier` (the
`upperRegion` branch lives) and `papers-craciun` (it dies).  These pins make the verdict a permanent,
regression-checked fact rather than a claim in a message.
-/

/-- info: 'CRNT.UpperRegionAdjudication.upperRegion_criterion_inconsistent_with_boundaryOmegaPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.UpperRegionAdjudication.upperRegion_criterion_inconsistent_with_boundaryOmegaPoint

/-- info: 'CRNT.UpperRegionAdjudication.comparableGrowthDescent_is_not_a_weaker_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.UpperRegionAdjudication.comparableGrowthDescent_is_not_a_weaker_route
