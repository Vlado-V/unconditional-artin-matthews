module

public import ArtinMatthews.MarkedMajorArcSiegelWalfisz
public import ArtinMatthews.MarkedMajorArcLowParameters


set_option backward.privateInPublic true
@[expose] public section

/-! The actual all-character Mangoldt main term at logarithmic modulus,
uniform throughout the full exponential length window. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology

 theorem marked_major_mangoldt_prefix_low (a η τ P : ℝ)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hP : 0 ≤ P) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ),
        (q:ℝ) ≤ L^a → Real.exp (τ*L) ≤ x → x ≤ Real.exp (η*L) →
        ‖(∑ n ∈ Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ))-
          (if χ=1 then (x:ℂ) else 0)‖ ≤ K*x*L^(-P) := by
  obtain ⟨M,hM,hSW⟩ := marked_all_character_mangoldt_log_bound (P+1) (a+1) (by linarith) (by linarith)
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hSW
  have hexp := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hτ)).eventually
    (eventually_ge_atTop x₀)
  refine ⟨M*τ^(-(P+1))+1,by positivity,?_⟩
  filter_upwards [hexp,marked_modulus_log_admissible a τ ha hτ,
    marked_conductor_correction_uniform a η τ P hη hτ,eventually_ge_atTop (1:ℝ)] with L hxbase hmod hcorr hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  intro q _ χ x hq hlo hhi
  have hxp : 0 < x := (Real.exp_pos _).trans_le hlo
  have hlog : τ*L ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hlo
  have hpow : (Real.log x)^(-(P+1)) ≤ τ^(-(P+1))*L^(-P) := by
    calc
      _ ≤ (τ*L)^(-(P+1)) := Real.rpow_le_rpow_of_nonpos (mul_pos hτ hLp) hlog (by linarith)
      _ = τ^(-(P+1))*L^(-(P+1)) := Real.mul_rpow hτ.le hLp.le
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (Real.rpow_nonneg hτ.le _)
  have hb := hx₀ x (hxbase.trans hlo) q χ (hmod (q:ℝ) x hq hlo)
  calc
    _ ≤ M*x*(Real.log x)^(-(P+1))+(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := hb
    _ ≤ M*x*(τ^(-(P+1))*L^(-P))+x*L^(-P) :=
      add_le_add (mul_le_mul_of_nonneg_left hpow (mul_pos hM hxp).le) (hcorr q x hq hlo hhi)
    _ = _ := by ring

end ArtinMatthews
