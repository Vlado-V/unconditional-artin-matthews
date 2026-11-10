module

public import ArtinMatthews.SourceFiniteKPRankOneTorus
public import ArtinMatthews.SourceFiniteKP2Projective
public import ArtinMatthews.SourceKPCompactDiagonal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized rank-one diagonal representatives give the actual
torus in the local projective cover. Their ordinary scalar intersection
is trivial and every lifted projective diagonal has such a representative. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

def sourcePGL2DiagonalHom (F : Type*) [Field F] : Fˣ →* PGL(2, F) :=
  ProjGenLinGroup.mk.comp (sourceGL2DiagonalHom F)

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

def sourceFiniteKPProjectiveTorusSubgroup : Subgroup (SourceFiniteKP2Projective K hζ P) :=
  (sourcePGL2DiagonalHom (P.adicCompletion K)).range.comap (sourceFiniteKP2ProjectiveProjection K hζ P)

abbrev SourceFiniteKPProjectiveTorus := sourceFiniteKPProjectiveTorusSubgroup K hζ P

def sourceFiniteKPRankOneToProjective : SourceFiniteKPRankOneTorus K hζ P →*
    SourceFiniteKPProjectiveTorus K hζ P :=
  ((sourceFiniteKP2ProjectiveMk K hζ P).comp (sourceFiniteKPRankOneSubgroup K hζ P).subtype).codRestrict _ (by
    intro x
    refine ⟨sourceFiniteKPRankOneBase K hζ P x, ?_⟩
    change ProjGenLinGroup.mk (sourceGL2Diagonal (sourceFiniteKPRankOneBase K hζ P x)) =
      sourceFiniteKP2ProjectiveProjection K hζ P (sourceFiniteKP2ProjectiveMk K hζ P x.val)
    rw [sourceFiniteKP2ProjectiveProjection_mk, sourceFiniteKPRankOne_base_eq K hζ P x])

theorem sourceFiniteKPRankOneToProjective_injective : Function.Injective (sourceFiniteKPRankOneToProjective K hζ P) := by
  intro x y he
  have h : sourceFiniteKP2ProjectiveMk K hζ P x.val = sourceFiniteKP2ProjectiveMk K hζ P y.val :=
    congrArg Subtype.val he
  obtain ⟨s, ⟨u, rfl⟩, hxy⟩ := (QuotientGroup.mk'_eq_mk' _).mp h
  have hb := congrArg SourceFiniteKP2Cover.base hxy
  have h11 := congrArg (fun g : GL (Fin 2) (P.adicCompletion K) => g 1 1) hb
  change (x.val.base * GeneralLinearGroup.scalar (Fin 2) u) 1 1 = y.val.base 1 1 at h11
  rw [sourceGL2_right_scalar_apply, sourceFiniteKPRankOne_base_eq K hζ P x,
    sourceFiniteKPRankOne_base_eq K hζ P y] at h11
  change 1 * (u : P.adicCompletion K) = 1 at h11
  rw [one_mul] at h11
  have hu : u = 1 := Units.ext h11
  subst u
  apply Subtype.ext
  simpa only [map_one, mul_one] using hxy

theorem sourceFiniteKPRankOneToProjective_surjective :
    Function.Surjective (sourceFiniteKPRankOneToProjective K hζ P) := by
  intro y
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ P).range y.val
  change sourceFiniteKP2ProjectiveMk K hζ P g = y.val at hg
  have hy : ProjGenLinGroup.mk g.base ∈ (sourcePGL2DiagonalHom (P.adicCompletion K)).range := by
    rw [← sourceFiniteKP2ProjectiveProjection_mk K hζ P g, hg]
    exact y.property
  obtain ⟨a, ha⟩ := hy
  have ha' : ProjGenLinGroup.mk g.base = ProjGenLinGroup.mk (sourceGL2Diagonal a) := ha.symm
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp ha'
  let x : SourceFiniteKPRankOneTorus K hζ P := ⟨g * sourceFiniteKP2Scalar K hζ P u, ⟨a, hu.symm⟩⟩
  refine ⟨x, Subtype.ext ?_⟩
  change sourceFiniteKP2ProjectiveMk K hζ P (g * sourceFiniteKP2Scalar K hζ P u) = y.val
  rw [map_mul, sourceFiniteKP2ProjectiveMk_scalar, mul_one, hg]

def sourceFiniteKPProjectiveTorusEquiv : SourceFiniteKPRankOneTorus K hζ P ≃*
    SourceFiniteKPProjectiveTorus K hζ P :=
  MulEquiv.ofBijective (sourceFiniteKPRankOneToProjective K hζ P)
    ⟨sourceFiniteKPRankOneToProjective_injective K hζ P, sourceFiniteKPRankOneToProjective_surjective K hζ P⟩

end
end ArtinMatthews
