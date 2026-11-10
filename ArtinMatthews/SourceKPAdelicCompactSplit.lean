module

public import ArtinMatthews.SourceAdelicIwasawa
public import ArtinMatthews.SourceKPDeepCongruence
public import ArtinMatthews.SourceKPDeepPhase
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

/-! The actual global compact-model subgroup. It uses the full tame
integral groups, the explicit deep groups at wild places, and the
complex unitary factors. Its lift has central coordinate one. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicDeepCompactMatrix : Subgroup (GL (Fin 2) 𝔸[K]) where
  carrier := {g | g ∈ SourceKPAdelicBaseCompactMatrix K hζ ∧
    ∀ P : HeightOneSpectrum (𝓞 K), (6 : 𝓞 K) ∈ P.asIdeal →
      sourceKPAdelicBaseFiniteAt K P g ∈ (sourceKPDeepLocalBase K P).range}
  one_mem' := by
    refine ⟨(SourceKPAdelicBaseCompactMatrix K hζ).one_mem, ?_⟩
    intro P _
    rw [map_one]
    exact (sourceKPDeepLocalBase K P).range.one_mem
  mul_mem' := by
    rintro g h ⟨hg,hg'⟩ ⟨hh,hh'⟩
    refine ⟨(SourceKPAdelicBaseCompactMatrix K hζ).mul_mem hg hh, ?_⟩
    intro P hP
    rw [map_mul]
    exact (sourceKPDeepLocalBase K P).range.mul_mem (hg' P hP) (hh' P hP)
  inv_mem' := by
    rintro g ⟨hg,hg'⟩
    refine ⟨(SourceKPAdelicBaseCompactMatrix K hζ).inv_mem hg, ?_⟩
    intro P hP
    rw [map_inv]
    exact (sourceKPDeepLocalBase K P).range.inv_mem (hg' P hP)

def sourceKPAdelicDeepCompactFinite : sourceKPAdelicDeepCompactMatrix K hζ →* GL (Fin 2) 𝔸ᶠ[K] :=
  (MonoidHom.snd _ _).comp ((sourceKPGL2ProductEquiv K).toMonoidHom.comp
    (sourceKPAdelicDeepCompactMatrix K hζ).subtype)

def sourceKPAdelicDeepCompactInfinite :
    sourceKPAdelicDeepCompactMatrix K hζ →* GL (Fin 2) (InfiniteAdeleRing K) :=
  (MonoidHom.fst _ _).comp ((sourceKPGL2ProductEquiv K).toMonoidHom.comp
    (sourceKPAdelicDeepCompactMatrix K hζ).subtype)

theorem sourceKPAdelicDeepCompact_multiplier (g h : sourceKPAdelicDeepCompactMatrix K hζ) :
    sourceKPAdeleMultiplier K hζ (sourceKPAdelicDeepCompactFinite K hζ g)
      (sourceKPAdelicDeepCompactFinite K hζ h) = 1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro P
  change (sourceKPRootsTransport K hζ P).symm
    (sourceKPFiniteTwistedMultiplier K hζ P
      (sourceKPAdelicBaseFiniteAt K P g.val) (sourceKPAdelicBaseFiniteAt K P h.val)) = 1
  by_cases h6 : (6 : 𝓞 K) ∈ P.asIdeal
  · obtain ⟨u,hu⟩ := g.property.2 P h6
    obtain ⟨v,hv⟩ := h.property.2 P h6
    rw [← hu, ← hv]
    have hprod : SourceKPMatrixCubeData (sourceKPDeepLocalBase K P u * sourceKPDeepLocalBase K P v) := by
      rw [← map_mul]
      exact sourceKPDeepLocalBase_cubeData K P (u*v)
    rw [sourceKPFiniteTwistedMultiplier_deep K hζ P _ _
      (sourceKPDeepLocalBase_cubeData K P u) (sourceKPDeepLocalBase_cubeData K P v) hprod, map_one]
  · rw [sourceKPFiniteTwistedMultiplier_of_integral K hζ P h6 _ _
      (g.property.1.1 P) (h.property.1.1 P), map_one]

def sourceKPAdelicDeepCompactLift :
    sourceKPAdelicDeepCompactMatrix K hζ →* SourceKPAdelicProjective K hζ where
  toFun g := (ProjGenLinGroup.mk (sourceKPAdelicDeepCompactInfinite K hζ g),
    sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPAdelicDeepCompactFinite K hζ g))
  map_one' := by
    apply Prod.ext
    · change ProjGenLinGroup.mk (sourceKPAdelicDeepCompactInfinite K hζ 1) = 1
      rw [map_one, map_one]
    · change sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPAdelicDeepCompactFinite K hζ 1) = 1
      rw [map_one]
      exact (sourceKPFiniteAdeleProjectiveMk K hζ).map_one
  map_mul' g h := by
    apply Prod.ext
    · change ProjGenLinGroup.mk (sourceKPAdelicDeepCompactInfinite K hζ (g*h)) = _
      rw [map_mul, map_mul]
      rfl
    · change sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPAdelicDeepCompactFinite K hζ (g*h)) = _
      rw [map_mul]
      exact (sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ _ _
        (sourceKPAdelicDeepCompact_multiplier K hζ g h)).symm

def sourceKPAdelicDeepCompact : Subgroup (SourceKPAdelicProjective K hζ) :=
  (sourceKPAdelicDeepCompactLift K hζ).range

theorem sourceKPAdelicDeepCompactLift_projection (g : sourceKPAdelicDeepCompactMatrix K hζ) :
    sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicDeepCompactLift K hζ g) =
      ProjGenLinGroup.mk g.val := by
  apply (sourceKPAdelicProjectiveProductEquiv K).injective
  rw [sourceKPAdelicProjectiveProjection_product]
  rfl

theorem sourceKPAdelicDeepCompact_projection (g : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicProjectiveProjection K hζ g.val ∈ sourceKPAdelicBaseCompact K hζ := by
  obtain ⟨k,hk⟩ := g.property
  rw [← hk, sourceKPAdelicDeepCompactLift_projection]
  exact ⟨k.val,k.property.1,rfl⟩

end
end ArtinMatthews
