module

public import Mathlib.Order.Interval.Finset.Box
public import ArtinMatthews.SpectralCuspDoubleCosetRepresentatives
public import ArtinMatthews.SpectralGeometricSignSectors
public import ArtinMatthews.SpectralPoincareDoubleCosetKernel
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Actual finite reindexing of the positive geometric sum by the lower
matrix entry.  The fibers are the previously defined genuine modulus
fibers, and the grouped sum has proved finite support. -/

noncomputable section
open Set
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

theorem spectral_finsum_partition_fibres {α β : Type*} (F : α → ℂ) (g : α → β)
    (hF : Function.HasFiniteSupport F) :
    Function.HasFiniteSupport (fun b : β => ∑ᶠ a : {a : α // g a = b}, F a.val) ∧
      (∑ᶠ a : α, F a) = ∑ᶠ b : β, ∑ᶠ a : {a : α // g a = b}, F a.val := by
  classical
  let S := hF.toFinset
  have hS : Function.support F ⊆ (S : Set α) := by
    intro a ha
    exact hF.mem_toFinset.mpr ha
  have hfib (b : β) : (∑ᶠ a : {a : α // g a = b}, F a.val) = ∑ a ∈ S with g a = b, F a := by
    rw [finsum_subtype_eq_finsum_cond]
    apply finsum_cond_eq_sum_of_cond_iff F
    intro a ha
    constructor
    · intro h
      exact Finset.mem_filter.mpr ⟨hF.mem_toFinset.mpr ha,h⟩
    · intro h
      exact (Finset.mem_filter.mp h).2
  have he : (fun b : β => ∑ᶠ a : {a : α // g a = b}, F a.val) =
      fun b : β => ∑ a ∈ S with g a = b, F a := funext hfib
  have hSup := S.support_of_fiberwise_sum_subset_image F g
  rw [he]
  constructor
  · exact (S.image g).finite_toSet.subset hSup
  · rw [finsum_eq_sum_of_support_subset F hS,
      finsum_eq_sum_of_support_subset (fun b : β => ∑ a ∈ S with g a = b, F a) hSup]
    exact (Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩) F).symm

def gamma0PositiveCuspCorrespondence (N : ℕ) (r s : SL(2, ℤ)) :=
  {M : gamma0CuspCorrespondence N r s // 0 < M.val 1 0}

def gamma0PositiveCuspModulus (N : ℕ) (r s : SL(2, ℤ))
    (M : gamma0PositiveCuspCorrespondence N r s) : Ioi (0 : ℕ) :=
  ⟨(M.val.val 1 0).toNat,by
    have h : 0 < M.val.val 1 0 := M.property
    change 0 < (M.val.val 1 0).toNat
    omega⟩

def gamma0PositiveCuspModulusFibreEquiv (N : ℕ) (r s : SL(2, ℤ)) (c : Ioi (0 : ℕ)) :
    {M : gamma0PositiveCuspCorrespondence N r s // gamma0PositiveCuspModulus N r s M = c} ≃
      gamma0CuspMatrixFibre N r s c.val where
  toFun M := ⟨M.val.val.val,M.val.val.property,by
    have he : (M.val.val.val 1 0).toNat = c.val := congrArg Subtype.val M.property
    have hp : 0 < M.val.val.val 1 0 := M.val.property
    omega⟩
  invFun M := by
    let R : gamma0CuspCorrespondence N r s := ⟨M.val,M.property.1⟩
    let P : gamma0PositiveCuspCorrespondence N r s := ⟨R,by
      change 0 < M.val 1 0
      rw [M.property.2]
      exact_mod_cast (show 0 < c.val from c.property)⟩
    refine ⟨P,Subtype.ext ?_⟩
    change (M.val 1 0).toNat = c.val
    rw [M.property.2,Int.toNat_natCast]
  left_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv M := by apply Subtype.ext; rfl

theorem gamma0PositiveGeometricSum_modulus_fibres (N : ℕ) (r s : SL(2, ℤ))
    (ψ φ : h2SmoothCompactSeeds) :
    Function.HasFiniteSupport (fun c : Ioi (0 : ℕ) =>
      ∑ᶠ M : gamma0CuspMatrixFibre N r s c.val, compactPoincareGeometricKernel ψ φ M.val) ∧
      gamma0PositiveGeometricSum N r s ψ φ =
        ∑ᶠ c : Ioi (0 : ℕ), ∑ᶠ M : gamma0CuspMatrixFibre N r s c.val,
          compactPoincareGeometricKernel ψ φ M.val := by
  classical
  let F : gamma0PositiveCuspCorrespondence N r s → ℂ := fun M => compactPoincareGeometricKernel ψ φ M.val.val
  have hF : Function.HasFiniteSupport F :=
    Function.HasFiniteSupport.fun_comp_of_injective
      (g := fun M : gamma0PositiveCuspCorrespondence N r s => M.val.val)
      (Subtype.val_injective.comp Subtype.val_injective)
      (compactPoincareGeometricKernel_all_hasFiniteSupport ψ φ)
  have h := spectral_finsum_partition_fibres F (gamma0PositiveCuspModulus N r s) hF
  have he (c : Ioi (0 : ℕ)) : (∑ᶠ M : {M : gamma0PositiveCuspCorrespondence N r s //
      gamma0PositiveCuspModulus N r s M = c}, F M.val) =
      ∑ᶠ M : gamma0CuspMatrixFibre N r s c.val, compactPoincareGeometricKernel ψ φ M.val :=
    finsum_comp_equiv (f := fun M : gamma0CuspMatrixFibre N r s c.val => compactPoincareGeometricKernel ψ φ M.val)
      (gamma0PositiveCuspModulusFibreEquiv N r s c)
  have he' := funext he
  refine ⟨he' ▸ h.1,?_⟩
  calc
    _ = ∑ᶠ M : gamma0PositiveCuspCorrespondence N r s, F M := by
      let G : gamma0CuspCorrespondence N r s → ℂ := fun M => compactPoincareGeometricKernel ψ φ M.val
      let P : gamma0CuspCorrespondence N r s → Prop := fun M => 0 < M.val 1 0
      have hcond := finsum_subtype_eq_finsum_cond (f := G) P
      change (∑ᶠ M : Subtype P, G M.val) = ∑ᶠ M ∈ {M | P M}, G M at hcond
      rw [finsum_mem_def] at hcond
      calc
        _ = ∑ᶠ M : gamma0CuspCorrespondence N r s, ({M | P M}.indicator G) M := by
          unfold gamma0PositiveGeometricSum
          apply finsum_congr
          intro M
          by_cases hM : 0 < M.val 1 0 <;> simp [P,G,hM]
        _ = _ := hcond.symm
    _ = _ := he' ▸ h.2

end ArtinMatthews
