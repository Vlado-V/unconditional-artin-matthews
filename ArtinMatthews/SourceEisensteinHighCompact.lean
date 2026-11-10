module

public import ArtinMatthews.SourceEisensteinHighEnergy
public import ArtinMatthews.SourceEisensteinHighRemainder
public import ArtinMatthews.SourceKPCompactHeight
public import ArtinMatthews.SourceEisensteinHighRemainderContinuity
public import ArtinMatthews.SourceEisensteinNonconstantInvariance
public import ArtinMatthews.SourceKPHighCuspMeasure
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

/-! The actual high-cusp remainder and its native energy also descend through
the compact archimedean frame quotient. -/
namespace ArtinMatthews
open NumberField Matrix Topology Set MulOpposite
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ

abbrev SourceKPCompactHighCusp (T : ℝ) :=
  {x : Y // T < sourceKPAutomorphicCompactOrbitHeight K hζ x}

def sourceKPCompactHighCuspMk (T : ℝ) (x : SourceKPHighCuspAutomorphic K hζ T) :
    SourceKPCompactHighCusp K hζ T :=
  ⟨sourceKPAutomorphicCompactMk K hζ x.val,x.property⟩

theorem sourceKPCompactHighCuspMk_isOpenQuotientMap (T : ℝ) :
    IsOpenQuotientMap (sourceKPCompactHighCuspMk K hζ T) :=
  (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).restrictPreimage
    {x : Y | T < sourceKPAutomorphicCompactOrbitHeight K hζ x}

private theorem highCuspCompact_value_invariant {F : Type*}
    (T : ℝ)
    (f : SourceKPHighCuspAutomorphic K hζ T → F)
    (u : SourceKPAdelicProjective K hζ → F)
    (hval : ∀ (x : SourceKPHighCuspFinite K hζ T) q,
      sourceKPFiniteLevelMk K hζ q = x.val →
        f (sourceKPHighCuspProjection K hζ T x) = u q)
    (hcompact : ∀ (q : SourceKPAdelicProjective K hζ) (k : SourceKPArchCompactRightGroup K hζ),
      u (q.1*unop k.val,q.2) = u q)
    {x y : SourceKPHighCuspAutomorphic K hζ T}
    (hxy : sourceKPCompactHighCuspMk K hζ T x = sourceKPCompactHighCuspMk K hζ T y) :
    f x = f y := by
  have hk := congrArg Subtype.val hxy
  change (Quotient.mk _ x.val : Y) = Quotient.mk _ y.val at hk
  obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hk)
  obtain ⟨z,hz⟩ := sourceKPHighCusp_representative K hζ T y
  obtain ⟨q,hq⟩ := sourceKPFiniteLevelMk_surjective K hζ z.val
  have hy : sourceKPAutomorphicLevelMk K hζ q = y.val := by
    change (Quotient.mk _ (sourceKPFiniteLevelMk K hζ q) : SourceKPAutomorphicLevel K hζ) = _
    rw [hq]
    exact congrArg Subtype.val hz
  let q' : SourceKPAdelicProjective K hζ := (q.1*unop k.val,q.2)
  have hprod : q * ((unop k.val,1) : SourceKPAdelicProjective K hζ) = q' :=
    Prod.ext rfl (mul_one _)
  have hq' : T < sourceKPAdelicCoverHeight K hζ q' := by
    rw [← hprod,sourceKPAdelicCoverHeight_right_deep K hζ q
      ⟨(unop k.val,1),sourceKPArchCompactRight_deep K hζ k⟩,
      ← sourceKPFiniteLevelHeight_mk,hq]
    exact z.property
  let z' : SourceKPHighCuspFinite K hζ T := ⟨sourceKPFiniteLevelMk K hζ q',hq'⟩
  have hz' : sourceKPHighCuspProjection K hζ T z' = x := by
    apply Subtype.ext
    change sourceKPAutomorphicLevelMk K hζ q' = _
    rw [← sourceKPAutomorphicLevelMk_archRight K hζ k.val q,hy]
    exact hk
  calc
    f x = u q' := hz' ▸ hval z' q' rfl
    _ = u q := hcompact q k
    _ = f y := hz ▸ (hval z q hq).symm

private def sourceKPCompactHighCuspDescend {F : Type*} (T : ℝ)
    (f : SourceKPHighCuspAutomorphic K hζ T → F) :
    SourceKPCompactHighCusp K hζ T → F :=
  fun y => f (Classical.choose ((sourceKPCompactHighCuspMk_isOpenQuotientMap K hζ T).surjective y))

private theorem sourceKPCompactHighCuspDescend_mk {F : Type*} (T : ℝ)
    (f : SourceKPHighCuspAutomorphic K hζ T → F)
    (hf : ∀ x y, sourceKPCompactHighCuspMk K hζ T x = sourceKPCompactHighCuspMk K hζ T y → f x = f y)
    (x : SourceKPHighCuspAutomorphic K hζ T) :
    sourceKPCompactHighCuspDescend K hζ T f (sourceKPCompactHighCuspMk K hζ T x) = f x :=
  hf _ _ (Classical.choose_spec ((sourceKPCompactHighCuspMk_isOpenQuotientMap K hζ T).surjective _))

private theorem sourceKPCompactHighCuspDescend_continuous {F : Type*} [TopologicalSpace F]
    (T : ℝ) (f : SourceKPHighCuspAutomorphic K hζ T → F)
    (hf : ∀ x y, sourceKPCompactHighCuspMk K hζ T x = sourceKPCompactHighCuspMk K hζ T y → f x = f y)
    (hc : Continuous f) : Continuous (sourceKPCompactHighCuspDescend K hζ T f) := by
  apply (sourceKPCompactHighCuspMk_isOpenQuotientMap K hζ T).isQuotientMap.continuous_iff.mpr
  have he : sourceKPCompactHighCuspDescend K hζ T f ∘ sourceKPCompactHighCuspMk K hζ T = f :=
    funext (sourceKPCompactHighCuspDescend_mk K hζ T f hf)
  rw [he]
  exact hc

private theorem highCuspRemainder_compact_invariant (s : ℂ) (T : ℝ) (hT : 1 < T)
    (x y : SourceKPHighCuspAutomorphic K hζ T)
    (hxy : sourceKPCompactHighCuspMk K hζ T x = sourceKPCompactHighCuspMk K hζ T y) :
    sourceKPHighCuspNonconstantEisenstein K hζ s T hT x =
      sourceKPHighCuspNonconstantEisenstein K hζ s T hT y := by
  refine highCuspCompact_value_invariant K hζ T _ (sourceKPAdelicNonconstantEisenstein K hζ s) ?_ ?_ hxy
  · intro z q hq
    rw [sourceKPHighCuspNonconstantEisenstein_rep,← hq,sourceKPFiniteLevelNonconstantEisenstein_mk]
  · intro q k
    have h := sourceKPAdelicNonconstantEisenstein_deepCompact_right K hζ s q
      ⟨(unop k.val,1),sourceKPArchCompactRight_deep K hζ k⟩
    have he : q*((unop k.val,1) : SourceKPAdelicProjective K hζ) = (q.1*unop k.val,q.2) :=
      Prod.ext rfl (mul_one _)
    exact he ▸ h

def sourceKPCompactHighNonconstantEisenstein (s : ℂ) (T : ℝ) (hT : 1 < T) :
    SourceKPCompactHighCusp K hζ T → ℂ :=
  sourceKPCompactHighCuspDescend K hζ T (sourceKPHighCuspNonconstantEisenstein K hζ s T hT)

theorem sourceKPCompactHighNonconstantEisenstein_mk (s : ℂ) (T : ℝ) (hT : 1 < T)
    (x : SourceKPHighCuspAutomorphic K hζ T) :
    sourceKPCompactHighNonconstantEisenstein K hζ s T hT (sourceKPCompactHighCuspMk K hζ T x) =
      sourceKPHighCuspNonconstantEisenstein K hζ s T hT x :=
  sourceKPCompactHighCuspDescend_mk K hζ T _ (highCuspRemainder_compact_invariant K hζ s T hT) x

theorem sourceKPCompactHighNonconstantEisenstein_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) : Continuous (sourceKPCompactHighNonconstantEisenstein K hζ s T hT) :=
  sourceKPCompactHighCuspDescend_continuous K hζ T _ (highCuspRemainder_compact_invariant K hζ s T hT)
    (sourceKPHighCuspNonconstantEisenstein_continuous K hζ hs T hT)

private theorem highCuspEnergy_compact_invariant {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) (x y : SourceKPHighCuspAutomorphic K hζ T)
    (hxy : sourceKPCompactHighCuspMk K hζ T x = sourceKPCompactHighCuspMk K hζ T y) :
    sourceKPHighCuspNonconstantEnergy K hζ hs T hT x =
      sourceKPHighCuspNonconstantEnergy K hζ hs T hT y :=
  highCuspCompact_value_invariant K hζ T _ (sourceKPAdelicNonconstantEnergy K hζ s)
    (sourceKPHighCuspNonconstantEnergy_adelic K hζ hs T hT)
    (fun q k => sourceKPAdelicNonconstantEnergy_arch_right K hζ s q.1 (unop k.val) k.property q.2) hxy

def sourceKPCompactHighNonconstantEnergy {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) : SourceKPCompactHighCusp K hζ T → ℝ :=
  sourceKPCompactHighCuspDescend K hζ T (sourceKPHighCuspNonconstantEnergy K hζ hs T hT)

theorem sourceKPCompactHighNonconstantEnergy_mk {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) (x : SourceKPHighCuspAutomorphic K hζ T) :
    sourceKPCompactHighNonconstantEnergy K hζ hs T hT (sourceKPCompactHighCuspMk K hζ T x) =
      sourceKPHighCuspNonconstantEnergy K hζ hs T hT x :=
  sourceKPCompactHighCuspDescend_mk K hζ T _ (highCuspEnergy_compact_invariant K hζ hs T hT) x

theorem sourceKPCompactHighNonconstantEnergy_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) : Continuous (sourceKPCompactHighNonconstantEnergy K hζ hs T hT) :=
  sourceKPCompactHighCuspDescend_continuous K hζ T _ (highCuspEnergy_compact_invariant K hζ hs T hT)
    (sourceKPHighCuspNonconstantEnergy_continuous K hζ hs T hT)

end
end ArtinMatthews
