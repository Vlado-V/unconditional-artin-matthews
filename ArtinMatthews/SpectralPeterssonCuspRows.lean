module

public import ArtinMatthews.SpectralTrueWidthNormalizedMatrices
public import ArtinMatthews.SpectralGeometricSignSectors
public import ArtinMatthews.SpectralCuspBruhatKernel
public import ArtinMatthews.SpectralModularStripCountInjection
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

/-! Bottom rows of the actual cusp correspondence classify primitive
left-translation orbits. The sign is separated so the holomorphic
Poincare series can use the projective parabolic quotient. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0Petersson_left_translate_of_row_eq (N : ℕ) [NeZero N]
    (b a : SL(2, ℤ)) (M R : gamma0CuspCorrespondence N b a)
    (hc : R.val 1 0 = M.val 1 0) (hd : R.val 1 1 = M.val 1 1) :
    ∃ l : ℤ, R.val = integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*l)*M.val := by
  obtain ⟨k,hk⟩ := spectralModular_eq_translation_of_bottom_row_eq M.val R.val hc hd
  rw [← integerTranslation_eq_T_zpow] at hk
  have hR : a⁻¹*R.val*b ∈ CongruenceSubgroup.Gamma0 N := R.property
  have hM : a⁻¹*M.val*b ∈ CongruenceSubgroup.Gamma0 N := M.property
  have he : a⁻¹*integerTranslation k*a = (a⁻¹*R.val*b)*(a⁻¹*M.val*b)⁻¹ := by
    rw [hk]
    group
  have hT : a⁻¹*integerTranslation k*a ∈ CongruenceSubgroup.Gamma0 N := by
    rw [he]
    exact (CongruenceSubgroup.Gamma0 N).mul_mem hR ((CongruenceSubgroup.Gamma0 N).inv_mem hM)
  obtain ⟨l,hl⟩ := (gamma0CuspTrueWidth_translation_iff N a k).mp hT
  exact ⟨l, by rw [← hl]; exact hk⟩

theorem gamma0Petersson_normalized_translate (N : ℕ) [NeZero N]
    (b a M : SL(2, ℤ)) (l k : ℤ) :
    gamma0TrueWidthMatrix N b a
      (integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*l)*M*
        integerTranslation ((gamma0CuspTrueWidth N b : ℤ)*k)) =
      realTranslation (l : ℝ)*gamma0TrueWidthMatrix N b a M*realTranslation (k : ℝ) := by
  let wa := (gamma0CuspTrueWidth N a : ℝ)
  let wb := (gamma0CuspTrueWidth N b : ℝ)
  have ha : 0 < wa := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)
  have hb : 0 < wb := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N b)
  let Da := cuspWidthDilation wa ha
  let Db := cuspWidthDilation wb hb
  have hleft : Da⁻¹*realTranslation (wa*(l : ℝ)) = realTranslation (l : ℝ)*Da⁻¹ := by
    calc
      _ = Da⁻¹*(realTranslation (wa*(l : ℝ))*Da)*Da⁻¹ := by group
      _ = _ := by
        rw [← cuspWidthDilation_translation wa ha (l : ℝ)]
        change Da⁻¹*(Da*realTranslation (l : ℝ))*Da⁻¹ = realTranslation (l : ℝ)*Da⁻¹
        group
  have hright : realTranslation (wb*(k : ℝ))*Db = Db*realTranslation (k : ℝ) :=
    (cuspWidthDilation_translation wb hb (k : ℝ)).symm
  unfold gamma0TrueWidthMatrix
  rw [map_mul,map_mul,atkinRealMap_integerTranslation,atkinRealMap_integerTranslation]
  push_cast
  change Da⁻¹*(realTranslation (wa*(l : ℝ))*atkinRealMap M*
    realTranslation (wb*(k : ℝ)))*Db =
    realTranslation (l : ℝ)*(Da⁻¹*atkinRealMap M*Db)*realTranslation (k : ℝ)
  calc
    _ = (Da⁻¹*realTranslation (wa*(l : ℝ)))*atkinRealMap M*
        (realTranslation (wb*(k : ℝ))*Db) := by group
    _ = _ := by rw [hleft,hright]; group

theorem gamma0Petersson_normalized_left_translate (N : ℕ) [NeZero N]
    (b a M : SL(2, ℤ)) (l : ℤ) :
    gamma0TrueWidthMatrix N b a (integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*l)*M) =
      realTranslation (l : ℝ)*gamma0TrueWidthMatrix N b a M := by
  simpa only [mul_zero,integerTranslation_eq_T_zpow,zpow_zero,mul_one,Int.cast_zero,
    realTranslation_zero] using gamma0Petersson_normalized_translate N b a M l 0

theorem gamma0Petersson_normalized_neg (N : ℕ) [NeZero N] (b a M : SL(2, ℤ)) :
    gamma0TrueWidthMatrix N b a (-M) = -gamma0TrueWidthMatrix N b a M := by
  have hm : atkinRealMap (-M) = -atkinRealMap M := by
    ext i j
    change (((-M) i j : ℤ) : ℝ) = (-atkinRealMap M) i j
    simp [atkinRealMap]
  unfold gamma0TrueWidthMatrix
  rw [hm,mul_neg,neg_mul]

def Gamma0PeterssonSignedRow (N : ℕ) (b a : SL(2, ℤ)) :=
  {p : Fin 2 → ℤ // ∃ M : gamma0CuspCorrespondence N b a, (fun i => M.val 1 i) = p}

def gamma0PeterssonRowOfMatrix (N : ℕ) (b a : SL(2, ℤ))
    (M : gamma0CuspCorrespondence N b a) : Gamma0PeterssonSignedRow N b a :=
  ⟨fun i => M.val 1 i, ⟨M,rfl⟩⟩

def gamma0PeterssonRowMatrix (N : ℕ) (b a : SL(2, ℤ))
    (p : Gamma0PeterssonSignedRow N b a) : gamma0CuspCorrespondence N b a :=
  Classical.choose p.property

theorem gamma0PeterssonRowMatrix_row (N : ℕ) (b a : SL(2, ℤ))
    (p : Gamma0PeterssonSignedRow N b a) :
    (fun i => (gamma0PeterssonRowMatrix N b a p).val 1 i) = p.val :=
  Classical.choose_spec p.property

theorem gamma0PeterssonSignedRow_ne_zero (N : ℕ) (b a : SL(2, ℤ))
    (p : Gamma0PeterssonSignedRow N b a) : p.val ≠ 0 := by
  intro hp
  let M := (gamma0PeterssonRowMatrix N b a p).val
  have hM : (fun i => M 1 i) = (0 : Fin 2 → ℤ) :=
    (gamma0PeterssonRowMatrix_row N b a p).trans hp
  have hc : M 1 0 = 0 := congrFun hM 0
  have hd : M 1 1 = 0 := congrFun hM 1
  have he := M.det_coe
  rw [Matrix.det_fin_two,hc,hd] at he
  norm_num at he

def gamma0PeterssonSignedRowNeg (N : ℕ) (b a : SL(2, ℤ)) :
    Gamma0PeterssonSignedRow N b a ≃ Gamma0PeterssonSignedRow N b a where
  toFun p := ⟨-p.val, by
    obtain ⟨M,hM⟩ := p.property
    refine ⟨gamma0CuspCorrespondenceNeg N b a M,?_⟩
    funext i
    have h := congrFun hM i
    simp [gamma0CuspCorrespondenceNeg,h]⟩
  invFun p := ⟨-p.val, by
    obtain ⟨M,hM⟩ := p.property
    refine ⟨gamma0CuspCorrespondenceNeg N b a M,?_⟩
    funext i
    have h := congrFun hM i
    simp [gamma0CuspCorrespondenceNeg,h]⟩
  left_inv p := Subtype.ext (neg_neg p.val)
  right_inv p := Subtype.ext (neg_neg p.val)

end ArtinMatthews
