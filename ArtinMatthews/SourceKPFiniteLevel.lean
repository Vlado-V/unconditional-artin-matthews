module

public import ArtinMatthews.SourceKPFiniteSmoothSection
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

/-! The actual finite level, with its archimedean coordinate and finite coset
coordinate kept separately. No topology on the full finite cover is assumed. -/

namespace ArtinMatthews
open NumberField Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteDeepCoverLift_fst (k : sourceKPFiniteDeepMatrixGroup K) :
    (sourceKPFiniteDeepCoverLift K hζ k).1 = 1 := by
  rw [sourceKPFiniteDeepCoverLift_eq]
  change ProjGenLinGroup.mk
    ((sourceKPGL2ProductEquiv K (sourceKPFiniteMatrixEmbedding K k.val)).1) = 1
  rw [sourceKPFiniteMatrixEmbedding_product]
  exact map_one ProjGenLinGroup.mk

def sourceKPFiniteLevelLift :
    sourceKPFiniteDeepMatrixGroup K →* SourceKPFiniteAdeleProjective K hζ :=
  (MonoidHom.snd _ _).comp (sourceKPFiniteDeepCoverLift K hζ)

def sourceKPFiniteLevelSubgroup : Subgroup (SourceKPFiniteAdeleProjective K hζ) :=
  (sourceKPFiniteLevelLift K hζ).range

def SourceKPFiniteLevelFiber :=
  SourceKPFiniteAdeleProjective K hζ ⧸ sourceKPFiniteLevelSubgroup K hζ

instance : MulAction (SourceKPFiniteAdeleProjective K hζ) (SourceKPFiniteLevelFiber K hζ) :=
  inferInstanceAs (MulAction (SourceKPFiniteAdeleProjective K hζ)
    (SourceKPFiniteAdeleProjective K hζ ⧸ sourceKPFiniteLevelSubgroup K hζ))

abbrev SourceKPFiniteLevelSpace :=
  PGL(2, InfiniteAdeleRing K) × SourceKPFiniteLevelFiber K hζ

def sourceKPFiniteLevelMk (g : SourceKPAdelicProjective K hζ) :
    SourceKPFiniteLevelSpace K hζ := (g.1, QuotientGroup.mk g.2)

instance : MulAction (SourceKPAdelicProjective K hζ) (SourceKPFiniteLevelSpace K hζ) where
  smul g x := (g.1 * x.1, g.2 • x.2)
  one_smul x := Prod.ext (one_mul x.1) (one_smul _ x.2)
  mul_smul g h x := Prod.ext (mul_assoc g.1 h.1 x.1) (mul_smul g.2 h.2 x.2)

theorem sourceKPFiniteLevelMk_mul (g h : SourceKPAdelicProjective K hζ) :
    sourceKPFiniteLevelMk K hζ (g * h) = g • sourceKPFiniteLevelMk K hζ h := rfl

theorem sourceKPFiniteLevelMk_surjective : Function.Surjective (sourceKPFiniteLevelMk K hζ) := by
  rintro ⟨a,b⟩
  induction b using Quotient.inductionOn with
  | _ b => exact ⟨(a,b),rfl⟩

theorem sourceKPFiniteLevelMk_eq_iff (g h : SourceKPAdelicProjective K hζ) :
    sourceKPFiniteLevelMk K hζ g = sourceKPFiniteLevelMk K hζ h ↔
      ∃ k : sourceKPFiniteDeepMatrixGroup K, g * sourceKPFiniteDeepCoverLift K hζ k = h := by
  constructor
  · intro he
    have ha : g.1 = h.1 :=
      congrArg (fun x : SourceKPFiniteLevelSpace K hζ => x.1) he
    have hb : (QuotientGroup.mk g.2 : SourceKPFiniteLevelFiber K hζ) = QuotientGroup.mk h.2 :=
      congrArg (fun x : SourceKPFiniteLevelSpace K hζ => x.2) he
    obtain ⟨k,hk⟩ := QuotientGroup.eq.mp hb
    refine ⟨k, Prod.ext ?_ ?_⟩
    · change g.1 * (sourceKPFiniteDeepCoverLift K hζ k).1 = h.1
      rw [sourceKPFiniteDeepCoverLift_fst, mul_one, ha]
    · change g.2 * sourceKPFiniteLevelLift K hζ k = h.2
      rw [hk, mul_inv_cancel_left]
  · rintro ⟨k,rfl⟩
    apply Prod.ext
    · change g.1 = g.1 * (sourceKPFiniteDeepCoverLift K hζ k).1
      rw [sourceKPFiniteDeepCoverLift_fst, mul_one]
    · apply QuotientGroup.eq.mpr
      change g.2⁻¹ * (g.2 * sourceKPFiniteLevelLift K hζ k) ∈ sourceKPFiniteLevelSubgroup K hζ
      rw [inv_mul_cancel_left]
      exact ⟨k,rfl⟩

end
end ArtinMatthews
