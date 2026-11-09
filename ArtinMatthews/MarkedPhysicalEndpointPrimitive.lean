module

public import ArtinMatthews.MarkedPhysicalEndpointVectors


set_option backward.privateInPublic true
@[expose] public section

/-! The automatic-primitivity argument in PD03 after `det:lift`. The
possible zero determinant is retained until a genuine unshared prime
excludes it; no primitive-position assumption is substituted for the proof. -/
noncomputable section
namespace ArtinMatthews

theorem markedPhysicalMarkingProduct_coprime {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime) {M : ℕ}
    (a : MarkedPhysicalMarking P M) {s : ℕ} (hs : MarkedPhysicalBandRough P s) :
    (markedPhysicalMarkingProduct a).Coprime s := by
  apply Nat.Coprime.prod_left
  intro j _
  apply Nat.Coprime.prod_left
  intro k _
  exact (hP j _ (a j k).2).coprime_iff_not_dvd.mpr (hs j _ (a j k).2)

theorem markedPhysical_lift_primitive_or_zero {D b a m s r n : ℕ} {W : ℝ}
    (hrough : ∀ p : ℕ, p.Prime → p ∣ s → W ≤ (p : ℝ))
    (hcop : (D*b).Coprime s)
    (hsmall : |((b : ℤ)*m*n-(a : ℤ)*r*s : ℤ)| < W) :
    (D*b*m).Coprime s ∨ (b : ℤ)*m*n-(a : ℤ)*r*s = 0 := by
  by_cases hc : (D*b*m).Coprime s
  · exact Or.inl hc
  · right
    obtain ⟨p, hp, hpm, hps⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpG : ¬ p ∣ D*b := fun h => hp.not_dvd_one (by
      have hg := Nat.dvd_gcd h hps
      simpa only [hcop.gcd_eq_one] using hg)
    have hpm' : p ∣ m := (hp.dvd_mul.mp hpm).resolve_left hpG
    have hpt : (p : ℤ) ∣ (b : ℤ)*m*n-(a : ℤ)*r*s := by
      apply dvd_sub
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by exact_mod_cast hpm') _) _
      · exact dvd_mul_of_dvd_right (by exact_mod_cast hps) _
    by_contra ht
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr ht) (Int.natAbs_dvd_natAbs.mpr hpt)
    have hleZ : (p : ℤ) ≤ |(b : ℤ)*m*n-(a : ℤ)*r*s| := by
      have hle' : (((p : ℤ).natAbs : ℕ) : ℤ) ≤
          (((b : ℤ)*m*n-(a : ℤ)*r*s).natAbs : ℤ) := by exact_mod_cast hle
      simpa only [Int.natAbs_natCast, Int.natCast_natAbs] using hle' 
    have hleR : (p : ℝ) ≤ |((b : ℤ)*m*n-(a : ℤ)*r*s : ℤ)| := by
      exact_mod_cast hleZ
    exact (not_lt_of_ge ((hrough p hp hps).trans hleR)) hsmall

theorem markedPhysical_lift_det_ne_zero {b a m s r n p : ℕ}
    (hp : p.Prime) (hpb : p ∣ b) (hpa : ¬p ∣ a) (hpr : ¬p ∣ r) (hps : ¬p ∣ s) :
    (b : ℤ)*m*n-(a : ℤ)*r*s ≠ 0 := by
  intro ht
  have heq : b*m*n = a*r*s := by exact_mod_cast sub_eq_zero.mp ht
  have hd : p ∣ a*r*s := heq ▸ dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpb m) n
  rcases hp.dvd_mul.mp hd with har | hs
  · exact (hp.dvd_mul.mp har).elim hpa hpr
  · exact hps hs

theorem markedPhysical_lift_primitive {D b a m s r n p : ℕ} {W : ℝ}
    (hrough : ∀ l : ℕ, l.Prime → l ∣ s → W ≤ (l : ℝ))
    (hcop : (D*b).Coprime s)
    (hsmall : |((b : ℤ)*m*n-(a : ℤ)*r*s : ℤ)| < W)
    (hp : p.Prime) (hpb : p ∣ b) (hpa : ¬p ∣ a) (hpr : ¬p ∣ r) (hps : ¬p ∣ s) :
    (D*b*m).Coprime s :=
  (markedPhysical_lift_primitive_or_zero hrough hcop hsmall).resolve_right
    (markedPhysical_lift_det_ne_zero hp hpb hpa hpr hps)

end ArtinMatthews
