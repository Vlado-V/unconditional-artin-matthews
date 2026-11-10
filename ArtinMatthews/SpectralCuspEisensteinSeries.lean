module

public import ArtinMatthews.SpectralCuspEisensteinRows
public import ArtinMatthews.SpectralCuspTrueWidth
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
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

/-! The genuine source-cusp Eisenstein family in the convergent half-plane.
The factor `w_s^(-s)` is forced by the actual determinant-one source scaling. -/
noncomputable section
open Set Filter Matrix
open scoped MatrixGroups
namespace ArtinMatthews

def cuspEisensteinRowHeight (N : ℕ) (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) : ℝ :=
  ((gamma0CuspEisensteinRowRepresentative N r a v).val • z).im

theorem cuspEisensteinRowHeight_pos (N : ℕ) (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    0 < cuspEisensteinRowHeight N r a v z := UpperHalfPlane.im_pos _

theorem cuspEisensteinRowHeight_row (N : ℕ) (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    cuspEisensteinRowHeight N r a v z = z.im / ‖(v.val 0:ℂ)*z+v.val 1‖^2 := by
  unfold cuspEisensteinRowHeight
  rw [ModularGroup.im_smul_eq_div_normSq,ModularGroup.denom_apply,Complex.normSq_eq_norm_sq]
  have h := gamma0CuspEisensteinRowRepresentative_spec N r a v
  rw [congrFun h 0,congrFun h 1]

theorem cuspEisensteinRowHeight_of_row (N : ℕ) (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (M : SL(2,ℤ)) (hM : M 1=v.val)
    (z : UpperHalfPlane) : cuspEisensteinRowHeight N r a v z = (M • z).im := by
  rw [cuspEisensteinRowHeight_row,ModularGroup.im_smul_eq_div_normSq,
    ModularGroup.denom_apply,Complex.normSq_eq_norm_sq,congrFun hM 0,congrFun hM 1]

def cuspEisensteinRowTerm (N : ℕ) (r a : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) : ℂ :=
  (cuspEisensteinRowHeight N r a v z:ℂ)^s

theorem cuspEisensteinRowTerm_norm (N : ℕ) (r a : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    ‖cuspEisensteinRowTerm N r a s v z‖ =
      z.im^s.re * ‖(v.val 0:ℂ)*z+v.val 1‖^(-(2*s.re)) := by
  rw [cuspEisensteinRowTerm,Complex.norm_cpow_eq_rpow_re_of_pos
    (cuspEisensteinRowHeight_pos N r a v z),cuspEisensteinRowHeight_row,
    Real.div_rpow z.im_pos.le (sq_nonneg _),
    ← Real.rpow_natCast_mul (norm_nonneg _) 2 s.re,
    div_eq_mul_inv,Real.rpow_neg (norm_nonneg _)]
  norm_num

theorem cuspEisensteinRowTerm_summable_norm (N : ℕ) (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    Summable (fun v : Gamma0CuspEisensteinRows N r a => ‖cuspEisensteinRowTerm N r a s v z‖) := by
  have h := (EisensteinSeries.summable_one_div_norm_rpow
    (show 2 < 2*s.re by linarith)).subtype (fun v => v ∈ range (gamma0CuspEisensteinRow N r a))
  apply (h.mul_left (z.im^s.re*(EisensteinSeries.r z)^(-(2*s.re)))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro v
  rw [cuspEisensteinRowTerm_norm,mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (EisensteinSeries.summand_bound z (show 0 ≤ 2*s.re by linarith) v.val)
    (Real.rpow_nonneg z.im_pos.le _)

theorem cuspEisensteinRowTerm_summable (N : ℕ) (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    Summable (fun v : Gamma0CuspEisensteinRows N r a => cuspEisensteinRowTerm N r a s v z) :=
  (cuspEisensteinRowTerm_summable_norm N r a s hs z).of_norm

def cuspEisensteinRowSum (N : ℕ) (r a : SL(2,ℤ)) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  (1/2:ℂ)*∑' v : Gamma0CuspEisensteinRows N r a, cuspEisensteinRowTerm N r a s v z

def gamma0CuspEisenstein (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (z : UpperHalfPlane) : ℂ :=
  (gamma0CuspTrueWidth N a:ℂ)^(-s)*cuspEisensteinRowSum N 1 a s z

theorem cuspEisensteinRowTerm_continuous (N : ℕ) (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (v : Gamma0CuspEisensteinRows N r a) :
    Continuous (cuspEisensteinRowTerm N r a s v) := by
  have hh : Continuous (cuspEisensteinRowHeight N r a v) := by
    change Continuous (fun z : UpperHalfPlane =>
      (SpecialLinearGroup.mapGL ℝ (gamma0CuspEisensteinRowRepresentative N r a v).val • z).im)
    exact UpperHalfPlane.continuous_im.comp (continuous_const_smul _)
  exact (Complex.continuous_ofReal_cpow_const (by linarith : 0 < s.re)).comp hh

theorem cuspEisensteinRowTerm_compact_majorant (N : ℕ) (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ u : Gamma0CuspEisensteinRows N r a → ℝ, Summable u ∧
      ∀ v z, z ∈ K → ‖cuspEisensteinRowTerm N r a s v z‖ ≤ u v := by
  obtain ⟨A,B,hB,hKB⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hK
  obtain ⟨M,hM⟩ := hK.bddAbove_image UpperHalfPlane.continuous_im.continuousOn
  let H : ℝ := max M 1
  have hH : 0 < H := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  let C : ℝ := H^s.re*(EisensteinSeries.r ⟨⟨A,B⟩,hB⟩)^(-(2*s.re))
  refine ⟨fun v => C*‖v.val‖^(-(2*s.re)),?_,?_⟩
  · exact ((EisensteinSeries.summable_one_div_norm_rpow
      (show 2 < 2*s.re by linarith)).subtype
      (fun v => v ∈ range (gamma0CuspEisensteinRow N r a))).mul_left C
  · intro v z hz
    have him : z.im ≤ H := (hM ⟨z,hz,rfl⟩).trans (le_max_left _ _)
    have hh := EisensteinSeries.summand_bound_of_mem_verticalStrip
      (show 0 ≤ 2*s.re by linarith) v.val hB (hKB hz)
    rw [cuspEisensteinRowTerm_norm]
    calc
      _ ≤ H^s.re*((EisensteinSeries.r ⟨⟨A,B⟩,hB⟩)^(-(2*s.re))*‖v.val‖^(-(2*s.re))) :=
        mul_le_mul (Real.rpow_le_rpow z.im_pos.le him (by linarith)) hh
          (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hH.le _)
      _ = _ := (mul_assoc _ _ _).symm

theorem cuspEisensteinRowSum_continuous (N : ℕ) (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) : Continuous (cuspEisensteinRowSum N r a s) := by
  have hloc : TendstoLocallyUniformly
      (fun t : Finset (Gamma0CuspEisensteinRows N r a) => fun z =>
        ∑ v ∈ t, (1/2:ℂ)*cuspEisensteinRowTerm N r a s v z)
      (cuspEisensteinRowSum N r a s) atTop := by
    unfold cuspEisensteinRowSum
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨u,hu,hb⟩ := cuspEisensteinRowTerm_compact_majorant N r a s hs hK
    have h := tendstoUniformlyOn_tsum
      (f := fun (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) =>
        (1/2:ℂ)*cuspEisensteinRowTerm N r a s v z)
      (s := K) (hu := hu.mul_left ‖(1/2:ℂ)‖)
      (fun v z hz => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hb v z hz) (norm_nonneg _))
    simpa only [tsum_mul_left] using h
  apply hloc.continuous
  exact (Eventually.of_forall (fun t => continuous_finsetSum t
    (fun v _ => continuous_const.mul (cuspEisensteinRowTerm_continuous N r a s hs v)))).frequently

theorem gamma0CuspEisenstein_continuous (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) : Continuous (gamma0CuspEisenstein N a s) :=
  continuous_const.mul (cuspEisensteinRowSum_continuous N 1 a s hs)

end ArtinMatthews
