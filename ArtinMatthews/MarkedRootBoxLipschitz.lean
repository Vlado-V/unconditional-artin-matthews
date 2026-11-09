module

public import ArtinMatthews.MarkedRootBoxFaces


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit normalized transport continuity on the actual root box.
The bounds are derived from the root matrix, including its reciprocal term. -/

noncomputable section
namespace ArtinMatthews

def markedRootBoxDomain : Set (ℝ × (ℝ × ℝ)) :=
  {p | p.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2.1 ∈ Set.Icc (1:ℝ) 16 ∧ p.2.2 ∈ Set.Icc (1:ℝ) 2}

def MarkedRootBoxClose (h : ℝ) (p q : ℝ × (ℝ × ℝ)) : Prop :=
  |p.1-q.1| ≤ h ∧ |p.2.1-q.2.1| ≤ h ∧ |p.2.2-q.2.2| ≤ h

theorem markedRoot_tau_bound {H r : ℝ} (_hH : 0 ≤ H) (hr : r ∈ Set.Icc (0:ℝ) 1)
    (z : Fin 2 → ℝ) (hz : ∀ i,|z i| ≤ H) : |markedTau r z| ≤ 2*H := by
  calc
    _ ≤ |z 0|+|r*z 1| := abs_add_le _ _
    _ = |z 0|+|r| *|z 1| := by rw [abs_mul]
    _ ≤ H+1*H := add_le_add (hz 0)
      (mul_le_mul (by simpa only [abs_of_nonneg hr.1] using hr.2) (hz 1) (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem markedRoot_tau_difference {H h r s : ℝ} (_hH : 0 ≤ H) (hh : 0 ≤ h)
    (z : Fin 2 → ℝ) (hz : ∀ i,|z i| ≤ H) (hrs : |r-s| ≤ h) :
    |markedTau r z-markedTau s z| ≤ H*h := by
  rw [show markedTau r z-markedTau s z=(r-s)*z 1 by unfold markedTau; ring,abs_mul]
  exact (mul_le_mul hrs (hz 1) (abs_nonneg _) hh).trans_eq (mul_comm _ _)

theorem markedRootBoxFirst_lipschitz {H h : ℝ} (hH : 0 ≤ H) (hh : 0 ≤ h)
    (z : Fin 2 → ℝ) (hz : ∀ i,|z i| ≤ H) (p q : ℝ × (ℝ × ℝ))
    (hp : p ∈ markedRootBoxDomain) (hq : q ∈ markedRootBoxDomain) (hpq : MarkedRootBoxClose h p q) :
    |markedRootBoxFirst z p-markedRootBoxFirst z q| ≤ 18*H*h := by
  have hτ := markedRoot_tau_bound hH hp.1 z hz
  have hd := markedRoot_tau_difference hH hh z hz hpq.1
  have ha : |q.2.1| ≤ 16 := by rw [abs_of_nonneg (by linarith [hq.2.1.1])]; exact hq.2.1.2
  calc
    _ = |(p.2.1-q.2.1)*markedTau p.1 z+q.2.1*(markedTau p.1 z-markedTau q.1 z)| := by
      congr 1
      unfold markedRootBoxFirst
      ring
    _ ≤ |p.2.1-q.2.1| *|markedTau p.1 z|+|q.2.1| *|markedTau p.1 z-markedTau q.1 z| := by
      simpa only [abs_mul] using abs_add_le ((p.2.1-q.2.1)*markedTau p.1 z)
        (q.2.1*(markedTau p.1 z-markedTau q.1 z))
    _ ≤ h*(2*H)+16*(H*h) := add_le_add
      (mul_le_mul hpq.2.1 hτ (abs_nonneg _) hh)
      (mul_le_mul ha hd (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem markedRootBoxSecond_lipschitz {H h U V : ℝ} (hH : 0 ≤ H) (hh : 0 ≤ h)
    (hUV : 1 ≤ U*V) (z : Fin 2 → ℝ) (hz : ∀ i,|z i| ≤ H)
    (p q : ℝ × (ℝ × ℝ)) (hp : p ∈ markedRootBoxDomain) (hq : q ∈ markedRootBoxDomain)
    (hpq : MarkedRootBoxClose h p q) :
    |markedRootBoxSecond U V z p-markedRootBoxSecond U V z q| ≤ 5*H*h := by
  have hτ := markedRoot_tau_bound hH hp.1 z hz
  have hd := markedRoot_tau_difference hH hh z hz hpq.1
  have hb : |q.2.2| ≤ 2 := by rw [abs_of_nonneg (by linarith [hq.2.2.1])]; exact hq.2.2.2
  have hbase : |p.2.2*markedTau p.1 z-q.2.2*markedTau q.1 z| ≤ 4*H*h := by
    calc
      _ = |(p.2.2-q.2.2)*markedTau p.1 z+q.2.2*(markedTau p.1 z-markedTau q.1 z)| := by
        congr 1
        ring
      _ ≤ |p.2.2-q.2.2| *|markedTau p.1 z|+|q.2.2| *|markedTau p.1 z-markedTau q.1 z| := by
        simpa only [abs_mul] using abs_add_le ((p.2.2-q.2.2)*markedTau p.1 z)
          (q.2.2*(markedTau p.1 z-markedTau q.1 z))
      _ ≤ h*(2*H)+2*(H*h) := add_le_add
        (mul_le_mul hpq.2.2 hτ (abs_nonneg _) hh)
        (mul_le_mul hb hd (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hpa : 0 < p.2.1 := lt_of_lt_of_le zero_lt_one hp.2.1.1
  have hqa : 0 < q.2.1 := lt_of_lt_of_le zero_lt_one hq.2.1.1
  have hW : 0 < U*V := lt_of_lt_of_le zero_lt_one hUV
  have hden : 1 ≤ U*V*p.2.1*q.2.1 := by
    have h1 := mul_le_mul hUV hp.2.1.1 (by norm_num : (0:ℝ) ≤ 1) hW.le
    have h2 := mul_le_mul h1 hq.2.1.1 (by norm_num : (0:ℝ) ≤ 1) (mul_pos hW hpa).le
    simpa only [one_mul] using h2
  have hid : z 1/(U*V*p.2.1)-z 1/(U*V*q.2.1) =
      z 1*(q.2.1-p.2.1)/(U*V*p.2.1*q.2.1) := by
    field_simp [hW.ne',hpa.ne',hqa.ne']
  have hinv : |z 1/(U*V*p.2.1)-z 1/(U*V*q.2.1)| ≤ H*h := by
    rw [hid,abs_div,abs_mul,abs_of_pos (mul_pos (mul_pos hW hpa) hqa)]
    apply (div_le_iff₀ (mul_pos (mul_pos hW hpa) hqa)).mpr
    have ha := hpq.2.1
    rw [abs_sub_comm] at ha
    exact (mul_le_mul (hz 1) ha (abs_nonneg _) hH).trans
      (le_mul_of_one_le_right (mul_nonneg hH hh) hden)
  calc
    _ = |(p.2.2*markedTau p.1 z-q.2.2*markedTau q.1 z)+
        (z 1/(U*V*p.2.1)-z 1/(U*V*q.2.1))| := by
      congr 1
      unfold markedRootBoxSecond
      ring
    _ ≤ |p.2.2*markedTau p.1 z-q.2.2*markedTau q.1 z|+
        |z 1/(U*V*p.2.1)-z 1/(U*V*q.2.1)| := abs_add_le _ _
    _ ≤ 4*H*h+H*h := add_le_add hbase hinv
    _ = _ := by ring

end ArtinMatthews
