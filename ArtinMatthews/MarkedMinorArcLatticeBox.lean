module

public import ArtinMatthews.MarkedMinorArcLatticeCoordinates
public import ArtinMatthews.MarkedMinorArcOperator


set_option backward.privateInPublic true
@[expose] public section

/-! Literal integer coordinate boxes for the good-state lattice. -/
namespace ArtinMatthews

/-- An integer axis containing the full real centered interval [-A,A]. -/
noncomputable def markedMinorAxisLength (A : ℝ) : ℕ := 2*⌈A⌉₊+1

noncomputable def markedMinorAxisOrigin (A : ℝ) : ℤ := -(⌈A⌉₊ : ℤ)

theorem markedMinorAxis_mem {A : ℝ} (p : ℤ) (hp : |(p : ℝ)| ≤ A) :
    p ∈ Finset.Ico (markedMinorAxisOrigin A)
      (markedMinorAxisOrigin A+(markedMinorAxisLength A : ℤ)) := by
  have hc : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  have hb := abs_le.mp hp
  have hleft : -(⌈A⌉₊ : ℤ) ≤ p := by exact_mod_cast (by linarith : -(⌈A⌉₊ : ℝ) ≤ p)
  have hright : p ≤ (⌈A⌉₊ : ℤ) := by exact_mod_cast hb.2.trans hc
  simp only [Finset.mem_Ico,markedMinorAxisOrigin,markedMinorAxisLength,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  omega

theorem markedMinorAxisLength_bounds {A : ℝ} (hA : 1 ≤ A) :
    A ≤ (markedMinorAxisLength A : ℝ) ∧ (markedMinorAxisLength A : ℝ) ≤ 5*A := by
  have hlo : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  have hhi := Nat.ceil_lt_add_one (by linarith : (0:ℝ)≤A)
  simp only [markedMinorAxisLength,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  constructor <;> linarith

/-- Explicit side parameters from the reduced primitive vector. The lower
bounds and area are retained, with stronger .8 and .5 upper exponents. -/
theorem markedMinorShearSides_bounds {Y C len : ℝ} (hY : 1 ≤ Y) (hC : 1 ≤ C)
    (hlen : 0 < len) (hlo : Y^(-4/5 : ℝ) ≤ len) (hhi : len ≤ 2*Y^(-1/2 : ℝ)) :
    (6*C/len)*(2*C*Y*len)=12*C^2*Y ∧
    3*C*Y^(1/2 : ℝ) ≤ 6*C/len ∧ 6*C/len ≤ 6*C*Y^(4/5 : ℝ) ∧
    2*C*Y^(1/5 : ℝ) ≤ 2*C*Y*len ∧ 2*C*Y*len ≤ 4*C*Y^(1/2 : ℝ) := by
  have hYp : 0 < Y := by linarith
  have hCp : 0 < C := by linarith
  have hh : Y^(1/2 : ℝ)*Y^(-1/2 : ℝ)=1 := by rw [← Real.rpow_add hYp]; norm_num
  have he : Y^(4/5 : ℝ)*Y^(-4/5 : ℝ)=1 := by rw [← Real.rpow_add hYp]; norm_num
  have h₁ : Y*Y^(-4/5 : ℝ)=Y^(1/5 : ℝ) := by
    nth_rw 1 [← Real.rpow_one Y]
    rw [← Real.rpow_add hYp]
    congr 1
    norm_num
  have h₂ : Y*Y^(-1/2 : ℝ)=Y^(1/2 : ℝ) := by
    nth_rw 1 [← Real.rpow_one Y]
    rw [← Real.rpow_add hYp]
    congr 1
    norm_num
  refine ⟨by field_simp; ring,?_,?_,?_,?_⟩
  · apply (le_div_iff₀ hlen).mpr
    calc
      _ ≤ (3*C*Y^(1/2 : ℝ))*(2*Y^(-1/2 : ℝ)) := mul_le_mul_of_nonneg_left hhi (by positivity)
      _ = _ := by rw [show 3*C*Y^(1/2 : ℝ)*(2*Y^(-1/2 : ℝ))=6*C*(Y^(1/2 : ℝ)*Y^(-1/2 : ℝ)) by ring,hh,mul_one]
  · apply (div_le_iff₀ hlen).mpr
    calc
      _ = (6*C*Y^(4/5 : ℝ))*Y^(-4/5 : ℝ) := by rw [mul_assoc,he,mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
  · have hh := mul_le_mul_of_nonneg_left hlo (show 0≤2*C*Y by positivity)
    nlinarith [h₁]
  · have hh := mul_le_mul_of_nonneg_left hhi (show 0≤2*C*Y by positivity)
    nlinarith [h₂]

/-- The actual integer box has area O(Y), lower side exponent .1, and
stronger upper side exponents .8 and .5, uniformly in all shears. -/
theorem markedMinorShear_integer_box_bounds {Y C len : ℝ} (hY : 1 ≤ Y) (hC : 1 ≤ C)
    (hlen : 0 < len) (hlo : Y^(-4/5 : ℝ) ≤ len) (hhi : len ≤ 2*Y^(-1/2 : ℝ)) :
    Y^(1/10 : ℝ) ≤ (markedMinorAxisLength (6*C/len) : ℝ) ∧
    Y^(1/10 : ℝ) ≤ (markedMinorAxisLength (2*C*Y*len) : ℝ) ∧
    (markedMinorAxisLength (6*C/len) : ℝ)*(markedMinorAxisLength (2*C*Y*len) : ℝ) ≤ 300*C^2*Y ∧
    (markedMinorAxisLength (6*C/len) : ℝ) ≤ 30*C*Y^(4/5 : ℝ) ∧
    (markedMinorAxisLength (2*C*Y*len) : ℝ) ≤ 20*C*Y^(1/2 : ℝ) := by
  have hs := markedMinorShearSides_bounds hY hC hlen hlo hhi
  have hhalf : 1 ≤ Y^(1/2 : ℝ) := Real.one_le_rpow hY (by norm_num)
  have hfifth : 1 ≤ Y^(1/5 : ℝ) := Real.one_le_rpow hY (by norm_num)
  have hC₀ : 0 ≤ C := by linarith
  have hA : 1 ≤ 6*C/len := by nlinarith [hs.2.1]
  have hB : 1 ≤ 2*C*Y*len := by nlinarith [hs.2.2.2.1]
  have hM := markedMinorAxisLength_bounds hA
  have hN := markedMinorAxisLength_bounds hB
  have hp₁ : Y^(1/10 : ℝ) ≤ Y^(1/2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
  have hp₂ : Y^(1/10 : ℝ) ≤ Y^(1/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact hp₁.trans ((le_mul_of_one_le_left (by positivity) (show 1≤3*C by linarith)).trans (hs.2.1.trans hM.1))
  · exact hp₂.trans ((le_mul_of_one_le_left (by positivity) (show 1≤2*C by linarith)).trans (hs.2.2.2.1.trans hN.1))
  · calc
      _ ≤ (5*(6*C/len))*(5*(2*C*Y*len)) := mul_le_mul hM.2 hN.2 (Nat.cast_nonneg _) (by positivity)
      _ = 25*((6*C/len)*(2*C*Y*len)) := by ring
      _ = _ := by rw [hs.1]; ring
  · nlinarith [hM.2,hs.2.2.1]
  · nlinarith [hN.2,hs.2.2.2.2]

/-- Actual good-state shear geometry: a positively oriented integral basis
puts every relevant lattice point into a literal finite integer rectangle
of area O(Y), retaining all source lower exponents and stronger upper ones. -/
theorem markedMinorShear_good_integer_box (α : ℝ) {Y C : ℝ} (hY : 1 ≤ Y)
    (hC : 1 ≤ C) (hg : MarkedMinorShearGood α Y) :
    ∃ h l a b L T : ℤ, ∃ M N : ℕ, h*b-l*a=1 ∧
      Y^(1/10 : ℝ) ≤ (M : ℝ) ∧ Y^(1/10 : ℝ) ≤ (N : ℝ) ∧
      (M : ℝ)*(N : ℝ) ≤ 300*C^2*Y ∧
      (M : ℝ) ≤ 30*C*Y^(4/5 : ℝ) ∧ (N : ℝ) ≤ 20*C*Y^(1/2 : ℝ) ∧
      ∀ p : ℤ × ℤ, |(p.1 : ℝ)+(p.2 : ℝ)*α| ≤ C → |(p.2 : ℝ)/Y| ≤ C →
        markedMinorBasisCoords h l a b p ∈ markedMinorBox L T M N := by
  have hYp : 0 < Y := by linarith
  obtain ⟨h,l,hl,hcop,hlo,hhi⟩ := markedMinorShear_good_primitive_vector α hY hg
  have hlen : 0 < markedMinorShearLength α Y h l := (Real.rpow_pos_of_pos hYp _).trans_le hlo
  obtain ⟨a,b,hd,hparallel⟩ := markedMinorShear_reduced_completion α hYp h l hl hcop
  have hcomp := markedMinorShear_completion_short hYp h l a b hlen
    (markedMinorShearLength_scale hYp h l hhi)
    (markedMinorShear_completion_length α hYp h l a b hl hd hparallel)
  let A := 6*C/markedMinorShearLength α Y h l
  let B := 2*C*Y*markedMinorShearLength α Y h l
  have hshape := markedMinorShear_integer_box_bounds hY hC hlen hlo hhi
  refine ⟨h,l,a,b,markedMinorAxisOrigin A,markedMinorAxisOrigin B,
    markedMinorAxisLength A,markedMinorAxisLength B,hd,hshape.1,hshape.2.1,
    hshape.2.2.1,hshape.2.2.2.1,hshape.2.2.2.2,?_⟩
  intro p hp hq
  have hb := markedMinorBasisCoords_bounds hYp (by linarith) h l a b hlen hcomp p hp hq
  exact Finset.mem_product.mpr ⟨markedMinorAxis_mem _ hb.1,markedMinorAxis_mem _ hb.2⟩

end ArtinMatthews
