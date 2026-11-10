module

public import ArtinMatthews.SourceKPNormalizedBorel
public import ArtinMatthews.SourceFiniteKP2Projective
public import ArtinMatthews.SourceFiniteKPRankOneTorus
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

/-! The actual Borel subgroup in the local projective cubic cover.
Normalized upper triangular representatives inject into the quotient.
Stripping the upper root coordinate gives a homomorphism to the
literal covering torus. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

def sourceFiniteKPNormalizedBorelSubgroup : Subgroup (SourceFiniteKP2Cover K hζ P) :=
  (sourceGL2NormalizedBorel (P.adicCompletion K)).comap (sourceFiniteKP2Projection K hζ P)

abbrev SourceFiniteKPNormalizedBorel := sourceFiniteKPNormalizedBorelSubgroup K hζ P

def sourceFiniteKPNormalizedBorelBase : SourceFiniteKPNormalizedBorel K hζ P →* (P.adicCompletion K)ˣ :=
  GeneralLinearGroup.det.comp ((sourceFiniteKP2Projection K hζ P).comp
    (sourceFiniteKPNormalizedBorelSubgroup K hζ P).subtype)

theorem sourceFiniteKPNormalizedBorel_bottom (b : SourceFiniteKPNormalizedBorel K hζ P) :
    b.val.base 1 0 = 0 ∧ b.val.base 1 1 = 1 := b.property

def sourceFiniteKPNormalizedBorelToTorus : SourceFiniteKPNormalizedBorel K hζ P →*
    SourceFiniteKPRankOneTorus K hζ P where
  toFun g := ⟨⟨g.val.central, sourceGL2Diagonal (sourceFiniteKPNormalizedBorelBase K hζ P g)⟩,
    ⟨sourceFiniteKPNormalizedBorelBase K hζ P g, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    apply SourceFiniteKP2Cover.ext
    · rfl
    · change sourceGL2Diagonal (sourceFiniteKPNormalizedBorelBase K hζ P 1) = 1
      rw [map_one]
      exact (sourceGL2DiagonalHom (P.adicCompletion K)).map_one
  map_mul' g h := by
    apply Subtype.ext
    apply SourceFiniteKP2Cover.ext
    · change g.val.central * h.val.central * sourceFiniteKP2Multiplier K hζ P g.val.base h.val.base =
        g.val.central * h.val.central * sourceFiniteKP2Multiplier K hζ P
          (sourceGL2Diagonal (sourceFiniteKPNormalizedBorelBase K hζ P g))
          (sourceGL2Diagonal (sourceFiniteKPNormalizedBorelBase K hζ P h))
      rw [sourceFiniteKP2Multiplier_rankOne]
      exact congrArg (g.val.central * h.val.central * ·)
        (sourceKP2Multiplier_normalizedBorel (sourceFiniteKPHilbert K hζ P)
          g.val.base h.val.base g.property h.property)
    · change sourceGL2Diagonal (sourceFiniteKPNormalizedBorelBase K hζ P (g * h)) =
        sourceGL2Diagonal (sourceFiniteKPNormalizedBorelBase K hζ P g) *
          sourceGL2Diagonal (sourceFiniteKPNormalizedBorelBase K hζ P h)
      rw [map_mul]
      exact (sourceGL2DiagonalHom (P.adicCompletion K)).map_mul _ _

def sourceFiniteKPNormalizedBorelLift (g : GL (Fin 2) (P.adicCompletion K))
    (hg : g ∈ sourceGL2NormalizedBorel (P.adicCompletion K)) : SourceFiniteKPNormalizedBorel K hζ P :=
  ⟨sourceFiniteKP2Lift K hζ P g, hg⟩

theorem sourceFiniteKPNormalizedBorelToTorus_lift (g : GL (Fin 2) (P.adicCompletion K))
    (hg : g ∈ sourceGL2NormalizedBorel (P.adicCompletion K)) :
    sourceFiniteKPNormalizedBorelToTorus K hζ P (sourceFiniteKPNormalizedBorelLift K hζ P g hg) =
      sourceFiniteKPRankOneLift K hζ P (GeneralLinearGroup.det g) := rfl

def sourceFiniteKPNormalizedBorelToProjective : SourceFiniteKPNormalizedBorel K hζ P →*
    SourceFiniteKP2Projective K hζ P :=
  (sourceFiniteKP2ProjectiveMk K hζ P).comp (sourceFiniteKPNormalizedBorelSubgroup K hζ P).subtype

abbrev SourceFiniteKPProjectiveBorel := (sourceFiniteKPNormalizedBorelToProjective K hζ P).range

theorem sourceFiniteKPNormalizedBorelToProjective_injective :
    Function.Injective (sourceFiniteKPNormalizedBorelToProjective K hζ P) := by
  intro x y h
  change sourceFiniteKP2ProjectiveMk K hζ P x.val = sourceFiniteKP2ProjectiveMk K hζ P y.val at h
  obtain ⟨s, ⟨u, rfl⟩, he⟩ := (QuotientGroup.mk'_eq_mk' _).mp h
  have hb := congrArg SourceFiniteKP2Cover.base he
  have h11 := congrArg (fun g : GL (Fin 2) (P.adicCompletion K) => g 1 1) hb
  change (x.val.base * GeneralLinearGroup.scalar (Fin 2) u) 1 1 = y.val.base 1 1 at h11
  rw [sourceGL2_right_scalar_apply, (sourceFiniteKPNormalizedBorel_bottom K hζ P x).2,
    (sourceFiniteKPNormalizedBorel_bottom K hζ P y).2, one_mul] at h11
  have hu : u = 1 := Units.ext h11
  subst u
  apply Subtype.ext
  simpa only [map_one, mul_one] using he

def sourceFiniteKPProjectiveBorelEquiv : SourceFiniteKPNormalizedBorel K hζ P ≃*
    SourceFiniteKPProjectiveBorel K hζ P := by
  let m := sourceFiniteKPNormalizedBorelToProjective K hζ P
  let f : SourceFiniteKPNormalizedBorel K hζ P →* SourceFiniteKPProjectiveBorel K hζ P :=
    m.codRestrict m.range (fun x => ⟨x, rfl⟩)
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact sourceFiniteKPNormalizedBorelToProjective_injective K hζ P (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx⟩ := y.property
    exact ⟨x, Subtype.ext hx⟩

theorem sourceFiniteKPProjectiveBorelEquiv_val (x : SourceFiniteKPNormalizedBorel K hζ P) :
    (sourceFiniteKPProjectiveBorelEquiv K hζ P x).val = sourceFiniteKP2ProjectiveMk K hζ P x.val := rfl

end
end ArtinMatthews
