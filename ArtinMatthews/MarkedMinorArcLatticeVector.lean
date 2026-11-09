module

public import ArtinMatthews.MarkedMinorArcDiophantine
public import ArtinMatthews.MarkedTypeIIGoodFirst
public import Mathlib.Analysis.Normed.Group.AddCircle


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive Dirichlet vectors for the actual sheared lattice. This replaces
only shortest-vector minimization; the good-state lower bound and final
box exponents will remain those in PD §4. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators

/-- A reduced Dirichlet approximation supplies an actual primitive lattice
vector, with both sheared coordinates at scale Y^(-1/2). -/
theorem markedMinorShear_dirichlet_vector (α : ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    ∃ h l : ℤ, 0 < l ∧ IsCoprime h l ∧ (l : ℝ) ≤ Y^(1/2 : ℝ) ∧
      |(h : ℝ)+(l : ℝ)*α| ≤ Y^(-1/2 : ℝ) := by
  have hYp : 0 < Y := by linarith
  let R := Y^(1/2 : ℝ)
  let n := ⌊R⌋₊
  have hR : 1 ≤ R := Real.one_le_rpow hY (by norm_num)
  have hn : 0 < n := Nat.floor_pos.mpr hR
  obtain ⟨r,herr,hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hn
  have hrp : (0:ℝ) < r.den := by exact_mod_cast r.pos
  have hc : IsCoprime r.num (r.den : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa only [Int.gcd_def,Int.natAbs_natCast] using r.reduced.gcd_eq_one
  refine ⟨-r.num,r.den,by exact_mod_cast r.pos,hc.neg_left,?_,?_⟩
  · exact (show (r.den : ℝ) ≤ n by exact_mod_cast hden).trans
      (Nat.floor_le (by positivity))
  · have hid : |(-r.num : ℤ)+((r.den : ℤ) : ℝ)*α| = (r.den : ℝ)*|α-(r:ℝ)| := by
      rw [← abs_of_pos hrp,← abs_mul]
      congr 1
      rw [Rat.cast_def]
      push_cast
      field_simp
      ring
    push_cast at hid ⊢
    rw [hid]
    calc
      _ ≤ (r.den : ℝ)*(1/(((n : ℝ)+1)*r.den)) :=
        mul_le_mul_of_nonneg_left herr hrp.le
      _ = 1/((n : ℝ)+1) := by field_simp
      _ ≤ 1/R := one_div_le_one_div_of_le (by positivity) (Nat.lt_floor_add_one R).le
      _ = Y^(-1/2 : ℝ) := by
        rw [one_div,← Real.rpow_neg hYp.le]
        congr 1
        norm_num

/-- The exact Euclidean length of a sheared integer vector. -/
noncomputable def markedMinorShearLength (α Y : ℝ) (h l : ℤ) : ℝ :=
  Real.sqrt (((h : ℝ)+(l : ℝ)*α)^2+((l : ℝ)/Y)^2)

/-- The first good-state shear condition, in exactly the paper's circle
norm and exponents. Positive integer denominators include the source cutoff. -/
def MarkedMinorShearGood (α Y : ℝ) : Prop :=
  ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y^(1/5 : ℝ) →
    Y^(-7/10 : ℝ) < ‖(((l : ℝ)*α : ℝ) : AddCircle (1:ℝ))‖

/-- Actual good roots, with any real lift of D*r, satisfy the shear test. -/
theorem markedMinorShearGood_of_firstGood {ι : Type*} [Fintype ι]
    (D : ι → ℕ) (i : ι) (r : AddCircle (1:ℝ)) {α Y : ℝ}
    (hα : (α : AddCircle (1:ℝ)) = (D i) • r)
    (hgood : r ∉ markedFirstBadRoots D ⌊Y^(1/5 : ℝ)⌋₊ (Y^(-7/10 : ℝ))) :
    MarkedMinorShearGood α Y := by
  intro l hl hly
  have hln : l ≤ ⌊Y^(1/5 : ℝ)⌋₊ := Nat.le_floor hly
  have he : (((l : ℝ)*α : ℝ) : AddCircle (1:ℝ)) = ((D i*l : ℕ) : ℤ) • r := by
    rw [← nsmul_eq_mul,AddCircle.coe_nsmul,hα,smul_smul,natCast_zsmul]
    congr 1
    exact Nat.mul_comm _ _
  rw [he]
  by_contra h
  apply hgood
  apply Set.mem_iUnion.mpr
  refine ⟨i,Set.mem_iUnion.mpr ⟨l,Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hl,hln⟩,?_⟩⟩⟩
  exact le_of_not_gt h

/-- Each actual sheared coordinate is bounded by its Euclidean length. -/
theorem markedMinorShearLength_coordinates (α Y : ℝ) (h l : ℤ) :
    |(h : ℝ)+(l : ℝ)*α| ≤ markedMinorShearLength α Y h l ∧
    |(l : ℝ)/Y| ≤ markedMinorShearLength α Y h l := by
  have hn := Real.sqrt_nonneg (((h : ℝ)+(l : ℝ)*α)^2+((l : ℝ)/Y)^2)
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg ((h : ℝ)+(l : ℝ)*α)) (sq_nonneg ((l : ℝ)/Y)))
  unfold markedMinorShearLength
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg ((h : ℝ)+(l : ℝ)*α),sq_nonneg ((l : ℝ)/Y)]

/-- Adding an integer does not change the actual unit-circle residue. -/
theorem markedMinorShear_residue (h l : ℤ) (α : ℝ) :
    (((h : ℝ)+(l : ℝ)*α : ℝ) : AddCircle (1:ℝ)) =
      (((l : ℝ)*α : ℝ) : AddCircle (1:ℝ)) := by
  have hh : ((h : ℝ) : AddCircle (1:ℝ)) = 0 := by
    have hm := AddSubgroup.zsmul_mem_zmultiples (1:ℝ) h
    rw [zsmul_eq_mul,mul_one] at hm
    exact (QuotientAddGroup.eq_zero_iff _).mpr hm
  rw [AddCircle.coe_add,hh,zero_add]

/-- The genuine first good-state test prevents a sheared primitive vector
from being shorter than Y^(-.8). This is the source lower-length bound. -/
theorem markedMinorShearLength_lower {α Y : ℝ} (hY : 1 ≤ Y)
    (hg : MarkedMinorShearGood α Y) (h l : ℤ) (hl : 0 < l) :
    Y^(-4/5 : ℝ) ≤ markedMinorShearLength α Y h l := by
  have hYp : 0 < Y := by linarith
  by_contra hc
  have hshort := lt_of_not_ge hc
  have hcoord := markedMinorShearLength_coordinates α Y h l
  have hlr : (0:ℝ) < l := by exact_mod_cast hl
  have hly : (l : ℝ) < Y^(1/5 : ℝ) := by
    have hh : (l : ℝ)/Y < Y^(-4/5 : ℝ) :=
      ((le_abs_self _).trans hcoord.2).trans_lt hshort
    have he : Y^(-4/5 : ℝ)*Y = Y^(1/5 : ℝ) := by
      nth_rw 2 [← Real.rpow_one Y]
      rw [← Real.rpow_add hYp]
      congr 1
      norm_num
    rwa [div_lt_iff₀ hYp,he] at hh
  have hln : (l.toNat : ℝ) = (l : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hl.le
  have hlt := hg l.toNat (by omega) (by rw [hln]; exact hly.le)
  rw [hln] at hlt
  have hres : ‖(((l : ℝ)*α : ℝ) : AddCircle (1:ℝ))‖ ≤ |(h : ℝ)+(l : ℝ)*α| := by
    rw [← markedMinorShear_residue h l α]
    exact QuotientAddGroup.norm_mk_le_norm
  have hexp : Y^(-4/5 : ℝ) ≤ Y^(-7/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
  exact (hlt.trans_le (hres.trans (hcoord.1.trans (hshort.le.trans hexp)))).false

/-- The primitive Dirichlet vector has the same Y^(-1/2) upper scale as
the shortest vector used in the paper, with an explicit harmless constant. -/
theorem markedMinorShearLength_upper {α Y : ℝ} (hY : 0 < Y) (h l : ℤ)
    (hl : 0 ≤ l) (hden : (l : ℝ) ≤ Y^(1/2 : ℝ))
    (herr : |(h : ℝ)+(l : ℝ)*α| ≤ Y^(-1/2 : ℝ)) :
    markedMinorShearLength α Y h l ≤ 2*Y^(-1/2 : ℝ) := by
  have ht : |(l : ℝ)/Y| ≤ Y^(-1/2 : ℝ) := by
    rw [abs_of_nonneg (div_nonneg (by exact_mod_cast hl) hY.le)]
    apply (div_le_div_of_nonneg_right hden hY.le).trans
    have he : Y^(1/2 : ℝ)/Y = Y^(-1/2 : ℝ) := by
      nth_rw 2 [← Real.rpow_one Y]
      rw [← Real.rpow_sub hY]
      congr 1
      norm_num
    exact he.le
  have hn := Real.sqrt_nonneg (((h : ℝ)+(l : ℝ)*α)^2+((l : ℝ)/Y)^2)
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg ((h : ℝ)+(l : ℝ)*α)) (sq_nonneg ((l : ℝ)/Y)))
  have hs₁ := (sq_le_sq₀ (abs_nonneg _) (Real.rpow_nonneg hY.le _)).mpr herr
  have hs₂ := (sq_le_sq₀ (abs_nonneg _) (Real.rpow_nonneg hY.le _)).mpr ht
  rw [sq_abs] at hs₁ hs₂
  unfold markedMinorShearLength
  nlinarith [Real.rpow_pos_of_pos hY (-1/2 : ℝ)]

/-- Actual primitive good-state vector with both retained paper scales.
The route uses a reduced Dirichlet vector in place of norm minimization. -/
theorem markedMinorShear_good_primitive_vector (α : ℝ) {Y : ℝ} (hY : 1 ≤ Y)
    (hg : MarkedMinorShearGood α Y) :
    ∃ h l : ℤ, 0 < l ∧ IsCoprime h l ∧
      Y^(-4/5 : ℝ) ≤ markedMinorShearLength α Y h l ∧
      markedMinorShearLength α Y h l ≤ 2*Y^(-1/2 : ℝ) := by
  obtain ⟨h,l,hl,hcop,hden,herr⟩ := markedMinorShear_dirichlet_vector α hY
  exact ⟨h,l,hl,hcop,markedMinorShearLength_lower hY hg h l hl,
    markedMinorShearLength_upper (by linarith) h l hl.le hden herr⟩

end ArtinMatthews
