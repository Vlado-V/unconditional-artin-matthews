module

public import ArtinMatthews.GiantSignedGhostCoordinateApply
public import ArtinMatthews.FiniteCoordinateInvariance
public import ArtinMatthews.GiantSignedGhostSymmetry
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Full memory symmetry and coordinate-fiber symmetry agree, and every
actual coordinate ghost preserves this common domain. -/
namespace ArtinMatthews
noncomputable section

theorem giantSignedGroupPermutation_transport {Q : Finset ℕ}
    {s t : GiantSignedGroupMemory Q} (h : s = t) (σ : Equiv.Perm (Fin t.1)) :
    (let e := finCongr (congrArg Sigma.fst h)
     (⟨s.1, s.2 ∘ (e.trans (σ.trans e.symm))⟩ : GiantSignedGroupMemory Q)) =
      ⟨t.1, t.2 ∘ σ⟩ := by
  cases h
  rfl

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}

def giantSignedMemoryGroupsPermute (x : GiantSignedMemoryGroups P)
    (σ : (g : B) → Equiv.Perm (Fin (x g).1)) : GiantSignedMemoryGroups P :=
  fun g => ⟨(x g).1, (x g).2 ∘ σ g⟩

def GiantSignedGhostPermutationInvariant (f : GiantSignedMemoryGroups P → ℂ) : Prop :=
  ∀ x σ, f (giantSignedMemoryGroupsPermute x σ) = f x

omit [Fintype B] in
theorem giantSignedMemoryGroupsPermute_single (x : GiantSignedMemoryGroups P)
    (g : B) (σ : Equiv.Perm (Fin (x g).1)) :
    giantSignedMemoryGroupsPermute x
      (Function.update (fun h => Equiv.refl (Fin (x h).1)) g σ) =
        Function.update x g ⟨(x g).1, (x g).2 ∘ σ⟩ := by
  funext h
  by_cases hh : h = g
  · subst h
    simp [giantSignedMemoryGroupsPermute]
  · simp only [giantSignedMemoryGroupsPermute, Function.update_of_ne hh,
      Equiv.refl_apply, Function.comp_def]

omit [Fintype B] in
theorem giantSignedGhostProductSymmetric_iff_update (f : GiantSignedMemoryGroups P → ℂ) :
    GiantSignedGhostProductSymmetric f ↔
      ∀ x g, GiantSignedGroupSymmetric (fun t => f (Function.update x g t)) := by
  constructor
  · intro hf x g
    simpa only [giantSignedMemorySplit_update] using hf g (giantSignedMemorySplit P g x).2
  · intro hf g y
    let x := (giantSignedMemorySplit P g).symm
      (⟨0, fun i => Fin.elim0 i⟩, y)
    have he : (fun t => Function.update x g t) =
        (fun t => (giantSignedMemorySplit P g).symm (t, y)) := by
      funext t
      rw [← giantSignedMemorySplit_update]
      simp only [x, Equiv.apply_symm_apply]
    have heF := congrArg (fun k => fun t => f (k t)) he
    rw [← heF]
    exact hf x g

omit [Fintype B] in
theorem giantSignedGhostPermutationInvariant_fibers (f : GiantSignedMemoryGroups P → ℂ)
    (hf : GiantSignedGhostPermutationInvariant f) : GiantSignedGhostProductSymmetric f := by
  apply (giantSignedGhostProductSymmetric_iff_update f).mpr
  intro x g n σ a
  let z := Function.update x g (⟨n, a⟩ : GiantSignedGroupMemory (P g))
  have hz : z g = ⟨n, a⟩ := Function.update_self g _ x
  let e := finCongr (congrArg Sigma.fst hz)
  let σ' : Equiv.Perm (Fin (z g).1) := e.trans (σ.trans e.symm)
  have hp : (⟨(z g).1, (z g).2 ∘ σ'⟩ : GiantSignedGroupMemory (P g)) = ⟨n, a ∘ σ⟩ := by
    exact giantSignedGroupPermutation_transport hz σ
  have h := hf z (Function.update (fun h => Equiv.refl (Fin (z h).1)) g σ')
  rw [giantSignedMemoryGroupsPermute_single, hp] at h
  simpa only [z, Function.update_idem] using h

theorem giantSignedGhostProductSymmetric_permutations (f : GiantSignedMemoryGroups P → ℂ)
    (hf : GiantSignedGhostProductSymmetric f) : GiantSignedGhostPermutationInvariant f := by
  intro x σ
  let R := fun g (a b : GiantSignedGroupMemory (P g)) =>
    ∃ τ : Equiv.Perm (Fin a.1), b = ⟨a.1, a.2 ∘ τ⟩
  refine finiteCoordinateInvariant R f ?_ x (giantSignedMemoryGroupsPermute x σ) ?_
  · intro z g t ht
    obtain ⟨τ, rfl⟩ := ht
    have h := (giantSignedGhostProductSymmetric_iff_update f).mp hf z g (z g).1 τ (z g).2
    simpa only [Function.update_eq_self] using h
  · intro g
    exact ⟨σ g, rfl⟩

omit [Fintype B] in
theorem giantSignedMemorySymmetric_group_fibers (f : GiantSignedMemory P → ℂ)
    (hf : GiantSignedMemorySymmetric f) :
    GiantSignedGhostProductSymmetric (fun x => f ((giantSignedMemoryGroupEquiv P).symm x)) := by
  apply giantSignedGhostPermutationInvariant_fibers
  intro x σ
  exact hf ((giantSignedMemoryGroupEquiv P).symm x) σ

theorem giantSignedGhostProductSymmetric_memory (f : GiantSignedMemoryGroups P → ℂ)
    (hf : GiantSignedGhostProductSymmetric f) :
    GiantSignedMemorySymmetric (fun m => f (giantSignedMemoryGroupEquiv P m)) := by
  intro m σ
  exact giantSignedGhostProductSymmetric_permutations f hf (giantSignedMemoryGroupEquiv P m) σ

omit [Fintype B] in
theorem giantSignedGhostCoordinateApply_symmetric
    (ν : ∀ g, P g → ℝ) (A C D : B → ℂ) (g : B)
    (f : GiantSignedMemoryGroups P → ℂ) (hf : GiantSignedGhostProductSymmetric f) :
    GiantSignedGhostProductSymmetric (giantSignedGhostCoordinateApply ν A C D g f) := by
  apply (giantSignedGhostProductSymmetric_iff_update _).mpr
  intro x j n σ a
  by_cases hj : j = g
  · subst j
    have h := giantSignedGhostGroupApply_symmetric (ν g) (A g) (C g) (D g)
      (fun t => f (Function.update x g t))
      ((giantSignedGhostProductSymmetric_iff_update f).mp hf x g) n σ a
    simpa only [giantSignedGhostCoordinateApply_update, Function.update_self,
      Function.update_idem] using h
  · have hgj : g ≠ j := Ne.symm hj
    simp only [giantSignedGhostCoordinateApply_update, Function.update_of_ne hgj]
    simp_rw [Function.update_comm hj]
    apply congrArg (fun H => giantSignedGhostGroupApply (ν g) (A g) (C g) (D g) H (x g))
    funext t
    exact (giantSignedGhostProductSymmetric_iff_update f).mp hf
      (Function.update x g t) j n σ a

end
end ArtinMatthews
