module

public import ComplexityModelClasses
public import ComplexityModel.Workspace

/-!
Public complexity API. The machine model defines P, NP, FP, and the two
oracle function classes on binary words. Oracle substitution proves
ComplexityModel.classEquality_of_pEqualsNP. The checked machine-level
transcript enumerator is exposed through
ComplexityModel.FPLogNP.candidate_bound.
-/
