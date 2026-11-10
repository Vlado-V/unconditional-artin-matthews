module

public import ArtinMatthews.SourceKPAdelicCoveringTorus
public import ArtinMatthews.SourceKPFiniteAdeleWeyl
public import ArtinMatthews.StandardLocalBallDilation
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

/-! The actual norm-one unit torus with cubic conditions at the places above six. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical Matrix
open scoped NumberField AdeleRing BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPInfiniteCoordinate (w : InfinitePlace K) : InfiniteAdeleRing K →+* w.Completion where
  toFun a := a w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def sourceKPIdeleInfiniteCoordinate (w : InfinitePlace K) : IdeleGroup (𝓞 K) K →* w.Completionˣ :=
  (Units.map (sourceKPInfiniteCoordinate K w).toMonoidHom).comp (sourceKPIdeleInfiniteUnit K)

def sourceKPIdeleFiniteCoordinate (P : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup (𝓞 K) K →* (P.adicCompletion K)ˣ :=
  (Units.map (sourceKPAdeleEval K P).toMonoidHom).comp (sourceKPIdeleFiniteUnit K)

def sourceKPAdelicUnitIdeles : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {x | (∀ P, sourceKPFiniteVal K P (sourceKPIdeleFiniteCoordinate K P x : P.adicCompletion K) = 1) ∧
    (∀ P, (6 : 𝓞 K) ∈ P.asIdeal → ∃ a : (P.adicCompletion K)ˣ, a^3 = sourceKPIdeleFiniteCoordinate K P x) ∧
    (∀ w, ‖(sourceKPIdeleInfiniteCoordinate K w x : w.Completion)‖ = 1)}
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro P
      rw [map_one, Units.val_one, map_one]
    · intro P _
      exact ⟨1, by rw [one_pow, map_one]⟩
    · intro w
      rw [map_one, Units.val_one, norm_one]
  mul_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_, ?_⟩
    · intro P
      rw [map_mul, Units.val_mul, map_mul, hx.1 P, hy.1 P, one_mul]
    · intro P hP
      obtain ⟨a, ha⟩ := hx.2.1 P hP
      obtain ⟨b, hb⟩ := hy.2.1 P hP
      exact ⟨a*b, by rw [mul_pow, ha, hb, map_mul]⟩
    · intro w
      rw [map_mul, Units.val_mul, norm_mul, hx.2.2 w, hy.2.2 w, one_mul]
  inv_mem' := by
    intro x hx
    refine ⟨?_, ?_, ?_⟩
    · intro P
      rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, hx.1 P, inv_one]
    · intro P hP
      obtain ⟨a, ha⟩ := hx.2.1 P hP
      exact ⟨a⁻¹, by rw [inv_pow, ha, map_inv]⟩
    · intro w
      rw [map_inv, Units.val_inv_eq_inv_val, norm_inv, hx.2.2 w, inv_one]

theorem sourceKPAdelicUnitIdeles_norm (x : sourceKPAdelicUnitIdeles K) :
    sourceKPIdeleAbsoluteNorm K x.val = 1 := by
  have hi : ‖(sourceKPIdeleInfiniteUnit K x.val : InfiniteAdeleRing K)‖ = 1 := by
    rw [InfiniteAdeleRing.norm_def]
    apply Finset.prod_eq_one
    intro w _
    change ‖(sourceKPIdeleInfiniteCoordinate K w x.val : w.Completion)‖ ^ w.mult = 1
    rw [x.property.2.2 w, one_pow]
  have hf : ‖(sourceKPIdeleFiniteUnit K x.val : 𝔸ᶠ[K])‖ = 1 := by
    rw [FiniteAdeleRing.norm_eq_finprod_of_unit]
    apply finprod_eq_one_of_forall_eq_one
    intro P
    change ‖(sourceKPIdeleFiniteCoordinate K P x.val : P.adicCompletion K)‖ = 1
    rw [sourceLocalNorm_eq_zpow K P _ (sourceKPIdeleFiniteCoordinate K P x.val).ne_zero]
    change (Ideal.absNorm P.asIdeal : ℝ) ^
      WithZero.log (sourceKPFiniteVal K P (sourceKPIdeleFiniteCoordinate K P x.val : P.adicCompletion K)) = 1
    rw [x.property.1 P, WithZero.log_one, zpow_zero]
  change ‖(sourceKPIdeleInfiniteUnit K x.val : InfiniteAdeleRing K)‖ *
    ‖(sourceKPIdeleFiniteUnit K x.val : 𝔸ᶠ[K])‖ = 1
  rw [hi, hf, one_mul]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicUnitIdeles_hilbert (P : HeightOneSpectrum (𝓞 K))
    (x y : sourceKPAdelicUnitIdeles K) :
    sourceFiniteKPHilbert K hζ P (sourceKPIdeleFiniteCoordinate K P x.val)
      (sourceKPIdeleFiniteCoordinate K P y.val) = 1 := by
  by_cases h6 : (6 : 𝓞 K) ∈ P.asIdeal
  · obtain ⟨a, ha⟩ := x.property.2.1 P h6
    rw [← ha, sourceFiniteKPHilbert_cube_left]
  · exact sourceFiniteKPHilbert_units K hζ P h6 _ _ (x.property.1 P) (y.property.1 P)

theorem sourceKPAdelicUnitIdeles_multiplier (x y : sourceKPAdelicUnitIdeles K) :
    sourceKPAdeleMultiplier K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] (sourceKPIdeleFiniteUnit K x.val))
      (sourceKPDiagonalHom 𝔸ᶠ[K] (sourceKPIdeleFiniteUnit K y.val)) = 1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro P
  rw [sourceKPAdeleLocalMultiplier_diagonal]
  change (sourceKPRootsTransport K hζ P).symm
    (sourceFiniteKPHilbert K hζ P (sourceKPIdeleFiniteCoordinate K P x.val)
      (sourceKPIdeleFiniteCoordinate K P y.val) ^ 2) = 1
  rw [sourceKPAdelicUnitIdeles_hilbert K hζ P x y, one_pow, map_one]

def sourceKPAdelicUnitDiagonalLift : sourceKPAdelicUnitIdeles K →* SourceKPAdelicProjective K hζ where
  toFun x := sourceKPAdelicProjectiveDiagonalLift K hζ x.val
  map_one' := sourceKPAdelicProjectiveDiagonalLift_one K hζ
  map_mul' x y := by
    apply Prod.ext
    · change sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K)
        (sourceKPIdeleInfiniteUnit K (x.val*y.val)) =
        sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K x.val) *
          sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K y.val)
      rw [map_mul, map_mul]
    · change sourceKPFiniteAdeleProjectiveLift K hζ
        (sourceKPDiagonalHom 𝔸ᶠ[K] (sourceKPIdeleFiniteUnit K (x.val*y.val))) =
        sourceKPFiniteAdeleProjectiveLift K hζ
          (sourceKPDiagonalHom 𝔸ᶠ[K] (sourceKPIdeleFiniteUnit K x.val)) *
        sourceKPFiniteAdeleProjectiveLift K hζ
          (sourceKPDiagonalHom 𝔸ᶠ[K] (sourceKPIdeleFiniteUnit K y.val))
      rw [sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ _ _
        (sourceKPAdelicUnitIdeles_multiplier K hζ x y), map_mul, map_mul]

def sourceKPAdelicUnitTorus : Subgroup (sourceKPAdelicCoveringTorus K hζ) :=
  ((sourceKPAdelicUnitDiagonalLift K hζ).codRestrict (sourceKPAdelicCoveringTorus K hζ)
    (fun x => sourceKPAdelicCoveringTorus_diagonal_mem K hζ x.val)).range

theorem sourceKPAdelicUnitTorus_mem (u : sourceKPAdelicUnitTorus K hζ) :
    ∃ x : sourceKPAdelicUnitIdeles K,
      u.val.val = sourceKPAdelicProjectiveDiagonalLift K hζ x.val := by
  obtain ⟨x, hx⟩ := u.property
  exact ⟨x, (congrArg Subtype.val hx).symm⟩

end
end ArtinMatthews
