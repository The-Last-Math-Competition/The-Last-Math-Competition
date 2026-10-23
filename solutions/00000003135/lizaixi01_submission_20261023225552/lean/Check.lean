import Main

-- This frozen audit intentionally checks generated declarations as well.
-- Their names are not used by the mathematical proof or a reusable API.
set_option linter.auxLemma false

#print axioms TLMC3135.CoadjointOrbits
#print axioms TLMC3135.Dual
#print axioms TLMC3135.E
#print axioms TLMC3135.G
#print axioms TLMC3135.Lie
#print axioms TLMC3135.UnitarilyEquivalent
#print axioms TLMC3135.UnitaryDual
#print axioms TLMC3135.UnitaryRep
#print axioms TLMC3135.UnitaryRep.V
#print axioms TLMC3135.UnitaryRep._sizeOf_1
#print axioms TLMC3135.UnitaryRep._sizeOf_inst
#print axioms TLMC3135.UnitaryRep.action
#print axioms TLMC3135.UnitaryRep.casesOn
#print axioms TLMC3135.UnitaryRep.complete
#print axioms TLMC3135.UnitaryRep.ctorIdx
#print axioms TLMC3135.UnitaryRep.inner
#print axioms TLMC3135.UnitaryRep.irreducible
#print axioms TLMC3135.UnitaryRep.mk
#print axioms TLMC3135.UnitaryRep.mk._flat_ctor
#print axioms TLMC3135.UnitaryRep.mk.inj
#print axioms TLMC3135.UnitaryRep.mk.injEq
#print axioms TLMC3135.UnitaryRep.mk.noConfusion
#print axioms TLMC3135.UnitaryRep.mk.sizeOf_spec
#print axioms TLMC3135.UnitaryRep.noConfusion
#print axioms TLMC3135.UnitaryRep.noConfusionType
#print axioms TLMC3135.UnitaryRep.nontrivial
#print axioms TLMC3135.UnitaryRep.normed
#print axioms TLMC3135.UnitaryRep.rec
#print axioms TLMC3135.UnitaryRep.recOn
#print axioms TLMC3135.UnitaryRep.strong_continuity
#print axioms TLMC3135.actual_lie_algebra
#print axioms TLMC3135.actual_lie_algebra._proof_1
#print axioms TLMC3135.actual_lie_algebra._proof_2
#print axioms TLMC3135.actual_lie_algebra._proof_3
#print axioms TLMC3135.adjoint
#print axioms TLMC3135.adjoint._proof_1
#print axioms TLMC3135.adjoint._proof_2
#print axioms TLMC3135.adjoint_eq_id
#print axioms TLMC3135.coadjoint
#print axioms TLMC3135.coadjoint._proof_1
#print axioms TLMC3135.coadjointAction
#print axioms TLMC3135.coadjointAction._proof_1
#print axioms TLMC3135.coadjointAction._proof_2
#print axioms TLMC3135.coadjointOrbitsSubsingleton
#print axioms TLMC3135.coadjoint_eq
#print axioms TLMC3135.coadjoint_orbit_nonempty
#print axioms TLMC3135.complex_submodule_dichotomy
#print axioms TLMC3135.conjugation
#print axioms TLMC3135.conjugation.eq_1
#print axioms TLMC3135.conjugation_eq_id
#print axioms TLMC3135.conjugation_smooth
#print axioms TLMC3135.distinct_unitary_classes
#print axioms TLMC3135.finite_group_card
#print axioms TLMC3135.generator
#print axioms TLMC3135.generator.eq_1
#print axioms TLMC3135.groupCharts
#print axioms TLMC3135.groupDiscrete
#print axioms TLMC3135.groupManifold
#print axioms TLMC3135.groupTopology
#print axioms TLMC3135.group_compact
#print axioms TLMC3135.group_hausdorff
#print axioms TLMC3135.group_nilpotent
#print axioms TLMC3135.group_second_countable
#print axioms TLMC3135.lieFiniteDimensional
#print axioms TLMC3135.lieUnique
#print axioms TLMC3135.lie_eq_zero
#print axioms TLMC3135.lie_finrank
#print axioms TLMC3135.model
#print axioms TLMC3135.model_finrank
#print axioms TLMC3135.no_bijective_correspondence
#print axioms TLMC3135.no_equivalence_between_orbits_and_unitary_dual
#print axioms TLMC3135.signAction
#print axioms TLMC3135.signAction._proof_1
#print axioms TLMC3135.signAction._proof_2
#print axioms TLMC3135.signAction.eq_1
#print axioms TLMC3135.signRep
#print axioms TLMC3135.signRep._proof_1
#print axioms TLMC3135.sign_generator_apply
#print axioms TLMC3135.smoothGroup
#print axioms TLMC3135.trivialAction
#print axioms TLMC3135.trivialRep
#print axioms TLMC3135.trivialRep._proof_1
#print axioms TLMC3135.trivial_generator_apply
#print axioms TLMC3135.trivial_not_equivalent_sign
#print axioms TLMC3135.unitarySetoid
#print axioms TLMC3135.unitarySetoid._proof_1
#print axioms TLMC3135.unitary_equivalence_refl
#print axioms TLMC3135.unitary_equivalence_symm
#print axioms TLMC3135.unitary_equivalence_trans

run_cmd do
  let expected : List String := ["TLMC3135.CoadjointOrbits", "TLMC3135.Dual", "TLMC3135.E", "TLMC3135.G", "TLMC3135.Lie", "TLMC3135.UnitarilyEquivalent", "TLMC3135.UnitaryDual", "TLMC3135.UnitaryRep", "TLMC3135.UnitaryRep.V", "TLMC3135.UnitaryRep._sizeOf_1", "TLMC3135.UnitaryRep._sizeOf_inst", "TLMC3135.UnitaryRep.action", "TLMC3135.UnitaryRep.casesOn", "TLMC3135.UnitaryRep.complete", "TLMC3135.UnitaryRep.ctorIdx", "TLMC3135.UnitaryRep.inner", "TLMC3135.UnitaryRep.irreducible", "TLMC3135.UnitaryRep.mk", "TLMC3135.UnitaryRep.mk._flat_ctor", "TLMC3135.UnitaryRep.mk.inj", "TLMC3135.UnitaryRep.mk.injEq", "TLMC3135.UnitaryRep.mk.noConfusion", "TLMC3135.UnitaryRep.mk.sizeOf_spec", "TLMC3135.UnitaryRep.noConfusion", "TLMC3135.UnitaryRep.noConfusionType", "TLMC3135.UnitaryRep.nontrivial", "TLMC3135.UnitaryRep.normed", "TLMC3135.UnitaryRep.rec", "TLMC3135.UnitaryRep.recOn", "TLMC3135.UnitaryRep.strong_continuity", "TLMC3135.actual_lie_algebra", "TLMC3135.actual_lie_algebra._proof_1", "TLMC3135.actual_lie_algebra._proof_2", "TLMC3135.actual_lie_algebra._proof_3", "TLMC3135.adjoint", "TLMC3135.adjoint._proof_1", "TLMC3135.adjoint._proof_2", "TLMC3135.adjoint_eq_id", "TLMC3135.coadjoint", "TLMC3135.coadjoint._proof_1", "TLMC3135.coadjointAction", "TLMC3135.coadjointAction._proof_1", "TLMC3135.coadjointAction._proof_2", "TLMC3135.coadjointOrbitsSubsingleton", "TLMC3135.coadjoint_eq", "TLMC3135.coadjoint_orbit_nonempty", "TLMC3135.complex_submodule_dichotomy", "TLMC3135.conjugation", "TLMC3135.conjugation.eq_1", "TLMC3135.conjugation_eq_id", "TLMC3135.conjugation_smooth", "TLMC3135.distinct_unitary_classes", "TLMC3135.finite_group_card", "TLMC3135.generator", "TLMC3135.generator.eq_1", "TLMC3135.groupCharts", "TLMC3135.groupDiscrete", "TLMC3135.groupManifold", "TLMC3135.groupTopology", "TLMC3135.group_compact", "TLMC3135.group_hausdorff", "TLMC3135.group_nilpotent", "TLMC3135.group_second_countable", "TLMC3135.lieFiniteDimensional", "TLMC3135.lieUnique", "TLMC3135.lie_eq_zero", "TLMC3135.lie_finrank", "TLMC3135.model", "TLMC3135.model_finrank", "TLMC3135.no_bijective_correspondence", "TLMC3135.no_equivalence_between_orbits_and_unitary_dual", "TLMC3135.signAction", "TLMC3135.signAction._proof_1", "TLMC3135.signAction._proof_2", "TLMC3135.signAction.eq_1", "TLMC3135.signRep", "TLMC3135.signRep._proof_1", "TLMC3135.sign_generator_apply", "TLMC3135.smoothGroup", "TLMC3135.trivialAction", "TLMC3135.trivialRep", "TLMC3135.trivialRep._proof_1", "TLMC3135.trivial_generator_apply", "TLMC3135.trivial_not_equivalent_sign", "TLMC3135.unitarySetoid", "TLMC3135.unitarySetoid._proof_1", "TLMC3135.unitary_equivalence_refl", "TLMC3135.unitary_equivalence_symm", "TLMC3135.unitary_equivalence_trans"]
  let actual := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC3135 |>.isPrefixOf n then some n.toString else none
  unless actual.all expected.contains && expected.all actual.contains do
    throwError "namespace coverage mismatch: {actual}"
  for n in actual do
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {actual.length}"
