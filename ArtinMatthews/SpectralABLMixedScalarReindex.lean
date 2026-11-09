module

public import ArtinMatthews.SpectralMixedCuspBesselPairing


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set OAI.Erdos970.ErdosKloosterman
open scoped MatrixGroups
noncomputable section

/-- Native orientation `(1/s, ∞; n, m)` before compensating the phase. -/
def gamma0MixedNativeModulusTerm (r s : ℕ) [NeZero r] [NeZero s]
    (m n : ℤ) (F : ℝ → ℂ) (q : Ioi (0 : ℕ)) : ℂ :=
  letI : NeZero q.val := ⟨q.property.ne'⟩
  let C := gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) 1 (q.val : ℝ)
  (gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 q.val n m/(C : ℂ))*F C

/-- The ABL orientation `(m,n)` with its original `1/c` weight and
normalized modulus `s * sqrt(r) * c`. -/
def gamma0MixedSourceModulusTerm (r s : ℕ) [NeZero s] (hcop : r.Coprime s)
    (m n : ℤ) (F : ℝ → ℂ) (c : {c : ℕ // 0 < c ∧ r.Coprime c}) : ℂ :=
  letI : NeZero c.val := ⟨c.property.1.ne'⟩
  let hrq := Nat.coprime_mul_iff_right.mpr ⟨hcop,c.property.2⟩
  (1/(c.val : ℂ))*standardSum (s*c.val)
    (m*spectral_inverseUnitRepresentative r (s*c.val) hrq) n*
      F ((s : ℝ)*Real.sqrt (r : ℝ)*(c.val : ℝ))

def gamma0MixedSourceCompensation (r s : ℕ) (b n : ℤ) : ℂ :=
  (((s : ℝ)*Real.sqrt (r : ℝ) : ℝ) : ℂ)*atkinPhase ((n : ℝ)*(b : ℝ)/(r : ℝ))

theorem gamma0MixedSourceCompensation_ne_zero (r s : ℕ) [NeZero r] [NeZero s] (b n : ℤ) :
    gamma0MixedSourceCompensation r s b n ≠ 0 := by
  have hr : 0 < (r : ℝ) := Nat.cast_pos.mpr (NeZero.pos r)
  have hs : 0 < (s : ℝ) := Nat.cast_pos.mpr (NeZero.pos s)
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hs (Real.sqrt_pos.2 hr)).ne')
    (Complex.exp_ne_zero _)

theorem gamma0MixedNativeModulusTerm_zero_off_range (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (m n : ℤ) (F : ℝ → ℂ) (q : Ioi (0 : ℕ))
    (hq : q ∉ range (gamma0MixedSourceModulus r s)) :
    gamma0MixedNativeModulusTerm r s m n F q = 0 := by
  letI : NeZero q.val := ⟨q.property.ne'⟩
  have hz := gamma0MixedKloosterman_zero_off_source_moduli r s q.val hcop hab m n
    (mt (gamma0MixedSourceModulus_mem_range r s q).mpr hq)
  simp only [gamma0MixedNativeModulusTerm,hz,zero_div,zero_mul]

theorem gamma0MixedSourceModulusTerm_eq (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (m n : ℤ) (F : ℝ → ℂ) (c : {c : ℕ // 0 < c ∧ r.Coprime c}) :
    gamma0MixedSourceCompensation r s b n *
      gamma0MixedNativeModulusTerm r s m n F (gamma0MixedSourceModulus r s c) =
        gamma0MixedSourceModulusTerm r s hcop m n F c := by
  letI : NeZero c.val := ⟨c.property.1.ne'⟩
  let C := gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) 1 (s*c.val : ℕ)
  have h := gamma0MixedKloosterman_source_weighted_standard r s c.val hcop c.property.2 hab m n
  dsimp only at h
  change _ = _ * F ((s : ℝ)*Real.sqrt (r : ℝ)*(c.val : ℝ))
  rw [← gamma0MixedCusp_trueModulus r s hcop c.val]
  change (((s : ℝ)*Real.sqrt (r : ℝ) : ℝ) : ℂ)*atkinPhase ((n : ℝ)*(b : ℝ)/(r : ℝ))*
      ((gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 (s*c.val) n m/(C : ℂ))*F C) = _
  rw [Complex.ofReal_div] at h
  linear_combination (F C)*h

/-- Exact mixed-cusp arithmetic reindexing for a scalar kernel of either
sign. It includes both summability and the compensating phase. -/
theorem gamma0MixedSourceModulus_tsum_reindex (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (m n : ℤ) (F : ℝ → ℂ) :
    (Summable (gamma0MixedNativeModulusTerm r s m n F) ↔
      Summable (gamma0MixedSourceModulusTerm r s hcop m n F)) ∧
    (∑' c, gamma0MixedSourceModulusTerm r s hcop m n F c) =
      gamma0MixedSourceCompensation r s b n*(∑' q, gamma0MixedNativeModulusTerm r s m n F q) := by
  let E := gamma0MixedSourceModulus r s
  let G := gamma0MixedNativeModulusTerm r s m n F
  let S := gamma0MixedSourceModulusTerm r s hcop m n F
  let K := gamma0MixedSourceCompensation r s b n
  have hE := gamma0MixedSourceModulus_injective r s
  have hzero (q : Ioi (0 : ℕ)) (hq : q ∉ range E) : G q = 0 :=
    gamma0MixedNativeModulusTerm_zero_off_range r s hcop hab m n F q hq
  have hterm : (fun c => K*G (E c)) = S :=
    funext (gamma0MixedSourceModulusTerm_eq r s hcop hab m n F)
  have hK : K ≠ 0 := gamma0MixedSourceCompensation_ne_zero r s b n
  have hs : Summable (G ∘ E) ↔ Summable G := hE.summable_iff hzero
  have hmul : Summable (fun c => K*G (E c)) ↔ Summable (G ∘ E) := summable_mul_left_iff hK
  have hsupport : Function.support G ⊆ range E := fun q hq =>
    by_contradiction (fun hq' => hq (hzero q hq'))
  have hS : Summable S ↔ Summable (G ∘ E) := by rw [← hterm]; exact hmul
  change (Summable G ↔ Summable S) ∧ (∑' c, S c) = K*(∑' q, G q)
  refine ⟨hs.symm.trans hS.symm,?_⟩
  rw [← hterm,tsum_mul_left]
  exact congrArg (K*·) (hE.tsum_eq hsupport)

end
end ArtinMatthews
