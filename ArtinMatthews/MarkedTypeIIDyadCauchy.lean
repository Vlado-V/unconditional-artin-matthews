module

public import ArtinMatthews.MarkedTypeIIDyadQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! Cauchy on the literal occupied label dyad costs only X/Y quotients.
The actual determinant and common-label collision sums remain separate. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

def markedTypeIIDyadQuotientRange (Hm Hn Y : ℝ) : ℕ := ⌈4*(Hm*Hn)/Y⌉₊

theorem markedTypeIIDyadQuotientRange_le {Hm Hn Y : ℝ}
    (hY : 0<Y) (hXY : Y≤Hm*Hn) :
    (markedTypeIIDyadQuotientRange Hm Hn Y:ℝ)≤5*(Hm*Hn)/Y := by
  have hX : 0≤Hm*Hn := hY.le.trans hXY
  have h₁ : 1≤(Hm*Hn)/Y := (one_le_div hY).mpr hXY
  have hc := Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) hX) hY.le)
  unfold markedTypeIIDyadQuotientRange
  apply hc.le.trans
  rw [mul_div_assoc (4:ℝ) (Hm*Hn) Y,mul_div_assoc (5:ℝ) (Hm*Hn) Y]
  linarith

theorem markedTypeIIOccupiedLabelEndpoints_bounds {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (M N : Finset ℕ)
    (Hm Hn Y : ℝ) (hHm : 0≤Hm) (hY : 0<Y)
    (hM : ∀ m∈M,0<m ∧ (m:ℝ)≤2*Hm) (hN : ∀ n∈N,0<n ∧ (n:ℝ)≤2*Hn) :
    ∀ a∈markedTypeIIOccupiedLabelEndpoints P Y M N,
      0<a.label ∧ 1≤a.value ∧ a.value≤a.label*markedTypeIIDyadQuotientRange Hm Hn Y := by
  intro a ha
  obtain ⟨ham,hη⟩ := Finset.mem_filter.mp ha
  obtain ⟨⟨b,m,n⟩,ht,rfl⟩ := Finset.mem_image.mp ham
  obtain ⟨hb,hm,hn⟩ := by simpa only [Finset.mem_product] using ht
  have hb₀ := markedMajorLabelSet_pos P hP hb
  refine ⟨hb₀,Nat.mul_pos (hM m hm).1 (hN n hn).1,?_⟩
  have hlabel : Y≤(b:ℝ) := by
    change markedTypeIILabelCutoff ((b:ℝ)/Y)≠0 at hη
    have h := (markedTypeIILabelCutoff_support hη).1
    simpa only [one_mul] using (le_div_iff₀ hY).mp h
  have hvalue : ((m*n:ℕ):ℝ)≤4*(Hm*Hn) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (2*Hm)*(2*Hn) := mul_le_mul (hM m hm).2 (hN n hn).2 (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  let B := markedTypeIIDyadQuotientRange Hm Hn Y
  have hB : 4*(Hm*Hn)/Y≤(B:ℝ) := Nat.le_ceil _
  have hmul : 4*(Hm*Hn)≤(b:ℝ)*(B:ℝ) := by
    calc
      _ ≤ (B:ℝ)*Y := (div_le_iff₀ hY).mp hB
      _ ≤ (B:ℝ)*(b:ℝ) := mul_le_mul_of_nonneg_left hlabel (Nat.cast_nonneg _)
      _ = _ := mul_comm _ _
  change m*n≤b*B
  exact_mod_cast hvalue.trans hmul

theorem markedTypeIISelectedLabelDyadSum_cauchy {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (M N : Finset ℕ)
    (Hm Hn Y : ℝ) (hHm : 0≤Hm) (hY : 0<Y)
    (hM : ∀ m∈M,0<m ∧ (m:ℝ)≤2*Hm) (hN : ∀ n∈N,0<n ∧ (n:ℝ)≤2*Hn)
    (α β F : ℕ → ℂ) (hF : ∀ h,‖F h‖≤1) :
    let E := markedTypeIIOccupiedLabelEndpoints P Y M N
    let B := markedTypeIIDyadQuotientRange Hm Hn Y
    let c := markedTypeIILabelEndpointCoefficient P Y α β
    ‖markedTypeIISelectedLabelDyadSum P Y M N α β F‖^2 ≤ (B:ℝ)*
      (markedTypeIIDeterminantSum E c+markedTypeIICollisionSum E (Finset.range B) c).re := by
  let E := markedTypeIIOccupiedLabelEndpoints P Y M N
  let B := markedTypeIIDyadQuotientRange Hm Hn Y
  let c := markedTypeIILabelEndpointCoefficient P Y α β
  have hE := markedTypeIIOccupiedLabelEndpoints_bounds P hP M N Hm Hn Y hHm hY hM hN
  dsimp only
  change _ ≤ (B:ℝ)*(markedTypeIIDeterminantSum E c+markedTypeIICollisionSum E (Finset.range B) c).re
  rw [markedTypeIISelectedLabelDyadSum_eq_filtered,
    markedTypeII_quotient_weight_reindex E B c (markedTypeIIQuotientDampedCore P F) hE]
  have hc := marked_typeII_cauchy E (Finset.range B) c (markedTypeIIQuotientDampedCore P F)
    (fun h _ => markedTypeIIQuotientDampedCore_norm_le P F h (hF h))
  rw [marked_typeII_square_eq_determinant_add_collisions_of_mul_bound E B c hE,
    Finset.card_range] at hc
  exact hc

end
end ArtinMatthews
