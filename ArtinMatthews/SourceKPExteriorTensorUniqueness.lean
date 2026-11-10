module

public import ArtinMatthews.SourceKPExteriorTensor
public import ArtinMatthews.SourceKPTameCyclicWhittakerUniqueness
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The local uniqueness theorem gives exact finite tensor
factorization. The scalar is the value on the actual distinguished
tensor, so every exterior spherical normalization is fixed. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators TensorProduct
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (SourceExteriorPrime K S₀))
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "V" => fun P : T => sourceKPTameSphericalCyclicSpace K hζ S₀ (Subtype.val P)
local notation "f₀" => fun P : T => sourceKPTameCyclicSphericalVector K hζ S₀ (Subtype.val P)
local notation "λ₀" => fun P : T => sourceKPTameCyclicWhittaker K hζ S₀ (Subtype.val P) hS
local notation "n₀" => fun (P : T) (x : HeightOneSpectrum.adicCompletion K (Subtype.val (Subtype.val P))) =>
  sourceFiniteKP2ProjectiveLift K hζ (Subtype.val (Subtype.val P)) (sourceGL2Upper x)
local notation "ρ₀" => fun P : T => sourceKPTameSphericalCyclicRepresentation K hζ S₀ (Subtype.val P)

theorem sourceKPExteriorMultilinearWhittaker_factor
    (M : MultilinearMap ℂ V ℂ)
    (hM : ∀ (P : T) (x : P.val.val.adicCompletion K) (v : (P : T) → V P),
      M (Function.update v P (ρ₀ P (n₀ P x) (v P))) =
        localFiniteCharacter K P.val.val x * M v)
    (v : (P : T) → V P) :
    M v = M f₀ * ∏ P : T, λ₀ P (v P) := by
  have hreplace (a : (P : T) → V P) (P : T) :
      M a = λ₀ P (a P) * M (Function.update a P (f₀ P)) := by
    let ℓ := M.toLinearMap a P
    have hℓ : ∀ (x : P.val.val.adicCompletion K) (f : V P),
        ℓ (ρ₀ P (n₀ P x) f) = localFiniteCharacter K P.val.val x * ℓ f := by
      intro x f
      simpa only [ℓ, MultilinearMap.toLinearMap_apply, Function.update_self, Function.update_idem] using
        hM P x (Function.update a P f)
    have h := LinearMap.congr_fun
      (sourceKPTameCyclicWhittakerFunctional_eq_smul K hζ S₀ P.val hS ℓ hℓ) (a P)
    change M (Function.update a P (a P)) = M (Function.update a P (f₀ P)) * λ₀ P (a P) at h
    rw [Function.update_eq_self] at h
    exact h.trans (mul_comm _ _)
  let replaced (s : Finset T) (P : T) : V P := if P ∈ s then f₀ P else v P
  have hproduct (s : Finset T) :
      M v = (∏ P ∈ s, λ₀ P (v P)) * M (replaced s) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, one_mul, replaced, Finset.notMem_empty, ite_false]
    | @insert P s hP ih =>
      have ha : replaced s P = v P := by simp only [replaced, hP, ite_false]
      have he : Function.update (replaced s) P (f₀ P) = replaced (insert P s) := by
        funext Q
        by_cases hQP : Q = P
        · subst Q
          simp only [Function.update_self, replaced, Finset.mem_insert_self, ite_true]
        · simp only [Function.update_of_ne hQP, replaced, Finset.mem_insert, hQP, false_or]
      calc
        _ = (∏ Q ∈ s, λ₀ Q (v Q)) * M (replaced s) := ih
        _ = (∏ Q ∈ s, λ₀ Q (v Q)) *
            (λ₀ P (v P) * M (replaced (insert P s))) := by rw [hreplace (replaced s) P, ha, he]
        _ = _ := by rw [Finset.prod_insert hP]; ring
  have h := hproduct Finset.univ
  have he : replaced Finset.univ = f₀ := by
    funext P
    exact ite_eq_left (Finset.mem_univ P)
  rw [he] at h
  exact h.trans (mul_comm _ _)

theorem sourceKPExteriorTensorWhittaker_unique
    (ℓ : SourceKPExteriorTensor K hζ S₀ T →ₗ[ℂ] ℂ)
    (hℓ : ∀ (P : T) (x : P.val.val.adicCompletion K) (v : (P : T) → V P),
      ℓ (PiTensorProduct.tprod ℂ (Function.update v P (ρ₀ P (n₀ P x) (v P)))) =
        localFiniteCharacter K P.val.val x * ℓ (PiTensorProduct.tprod ℂ v)) :
    ℓ = ℓ (sourceKPExteriorTensorSpherical K hζ S₀ T) • sourceKPExteriorTensorWhittaker K hζ S₀ T hS := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change ℓ (PiTensorProduct.tprod ℂ v) =
    ℓ (sourceKPExteriorTensorSpherical K hζ S₀ T) *
      sourceKPExteriorTensorWhittaker K hζ S₀ T hS (PiTensorProduct.tprod ℂ v)
  rw [sourceKPExteriorTensorWhittaker_tprod]
  exact sourceKPExteriorMultilinearWhittaker_factor K hζ S₀ T hS
    (ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ)) hℓ v

end
end ArtinMatthews
