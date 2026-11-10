module

public import ArtinMatthews.SourceKPAdelicCubeTorus
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import ArtinMatthews.SourceArchIwasawaCompletion
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

/-! Actual ideles supported at the infinite places and their cubic roots. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceArchOnlyIdele : (InfiniteAdeleRing K)ˣ →* IdeleGroup (𝓞 K) K where
  toFun a :=
    { val := (a.val, 1)
      inv := ((a⁻¹).val, 1)
      val_inv := Prod.ext a.val_inv (one_mul 1)
      inv_val := Prod.ext a.inv_val (one_mul 1) }
  map_one' := Units.ext rfl
  map_mul' a b := by
    apply Units.ext
    exact Prod.ext rfl (one_mul 1).symm

theorem sourceArchOnlyIdele_infinite (a : (InfiniteAdeleRing K)ˣ) :
    sourceKPIdeleInfiniteUnit K (sourceArchOnlyIdele K a) = a := by
  apply Units.ext
  change (Units.map (sourceKPAdeleInfiniteProjection K).toMonoidHom
    (sourceArchOnlyIdele K a)).val = a.val
  rw [Units.coe_map]
  rfl

theorem sourceArchOnlyIdele_finite (a : (InfiniteAdeleRing K)ˣ) :
    sourceKPIdeleFiniteUnit K (sourceArchOnlyIdele K a) = 1 := by
  apply Units.ext
  change (Units.map (sourceKPAdeleFiniteProjection K).toMonoidHom
    (sourceArchOnlyIdele K a)).val = (1 : 𝔸ᶠ[K])
  rw [Units.coe_map]
  rfl

theorem sourceArchOnlyIdele_norm (a : (InfiniteAdeleRing K)ˣ) :
    sourceKPIdeleAbsoluteNorm K (sourceArchOnlyIdele K a) = ‖(a : InfiniteAdeleRing K)‖ := by
  have hF : ‖(1 : 𝔸ᶠ[K])‖ = 1 := by
    have h := FiniteAdeleRing.norm_eq_finprod_of_unit (1 : 𝔸ᶠ[K]ˣ)
    change ‖(1 : 𝔸ᶠ[K])‖ = ∏ᶠ P : HeightOneSpectrum (𝓞 K), ‖(1 : P.adicCompletion K)‖ at h
    rw [h]
    simp
  change ‖(sourceKPIdeleInfiniteUnit K (sourceArchOnlyIdele K a) : InfiniteAdeleRing K)‖ *
    ‖(sourceKPIdeleFiniteUnit K (sourceArchOnlyIdele K a) : 𝔸ᶠ[K])‖ = _
  rw [sourceArchOnlyIdele_infinite, sourceArchOnlyIdele_finite, Units.val_one, hF, mul_one]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
include hζ

theorem sourceArchUnits_exists_cube (a : (InfiniteAdeleRing K)ˣ) :
    ∃ b : (InfiniteAdeleRing K)ˣ, b^3 = a := by
  have hav (v : InfinitePlace K) : (a : InfiniteAdeleRing K) v ≠ 0 := by
    intro hv
    have he := congrArg (fun x : InfiniteAdeleRing K => x v) a.val_inv
    change (a : InfiniteAdeleRing K) v * ((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v = 1 at he
    rw [hv, zero_mul] at he
    exact zero_ne_one he
  have hroot (v : InfinitePlace K) : ∃ b : v.Completion, b^3 = (a : InfiniteAdeleRing K) v := by
    let e := sourceKPArchComplexEquiv K hζ v
    obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (e ((a : InfiniteAdeleRing K) v)) (by decide : 0 < 3)
    refine ⟨e.symm z, ?_⟩
    apply e.injective
    rw [map_pow, e.apply_symm_apply, hz]
  choose b hb using hroot
  have hb0 (v : InfinitePlace K) : b v ≠ 0 := by
    intro he
    have h := hb v
    rw [he, zero_pow (by decide : 3 ≠ 0)] at h
    exact hav v h.symm
  let u : (InfiniteAdeleRing K)ˣ :=
    { val := fun v => b v
      inv := fun v => (b v)⁻¹
      val_inv := funext (fun v => mul_inv_cancel₀ (hb0 v))
      inv_val := funext (fun v => inv_mul_cancel₀ (hb0 v)) }
  refine ⟨u, ?_⟩
  apply Units.ext
  funext v
  change (b v)^3 = (a : InfiniteAdeleRing K) v
  exact hb v

theorem sourceArchOnlyIdele_mem_cubes (a : (InfiniteAdeleRing K)ˣ) :
    sourceArchOnlyIdele K a ∈ sourceKPIdeleCubeSubgroup K := by
  obtain ⟨b,hb⟩ := sourceArchUnits_exists_cube K hζ a
  refine ⟨sourceArchOnlyIdele K b, ?_⟩
  change (sourceArchOnlyIdele K b)^3 = sourceArchOnlyIdele K a
  rw [← map_pow, hb]

def sourceArchOnlyCubeIdele (a : (InfiniteAdeleRing K)ˣ) : SourceKPIdeleCubes K :=
  ⟨sourceArchOnlyIdele K a, sourceArchOnlyIdele_mem_cubes K hζ a⟩

theorem sourceArchOnlyCubeIdele_val (a : (InfiniteAdeleRing K)ˣ) :
    (sourceArchOnlyCubeIdele K hζ a).val = sourceArchOnlyIdele K a := rfl

end
end ArtinMatthews
