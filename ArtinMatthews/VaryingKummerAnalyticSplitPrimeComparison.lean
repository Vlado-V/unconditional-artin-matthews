module

public import ArtinMatthews.VaryingKummerAnalyticMixedExplicitFormulaBound


set_option backward.privateInPublic true
@[expose] public section

/-! Counting actual rational-prime norm fibers inside the nonnegative genuine
Dedekind prime-power sum.  Every counted prime ideal contributes its first
power; no prime-power removal or assumed prime-ideal theorem is used. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField OAI.PrimeDegreePackets Complex MeasureTheory Set
open scoped Classical ContDiff BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

abbrev NormPrimeFiber (S : Finset Nat.Primes) :=
  Σ p : S, ↥((idealsOverPrime K p.val).filter (fun Q => Ideal.absNorm Q = (p.val : ℕ)))

def normPrimeFiberEmbedding (S : Finset Nat.Primes) : NormPrimeFiber K S ↪ DedekindPrimePowerIndex K where
  toFun i := ⟨i.1.val,⟨⟨i.2.val,(Finset.mem_filter.mp i.2.property).1⟩,0⟩⟩
  inj' := by
    rintro ⟨⟨p,hp⟩,P⟩ ⟨⟨q,hq⟩,Q⟩ h
    have hpq := congrArg Sigma.fst h
    dsimp at hpq
    subst q
    have hPQ := congrArg (fun i : DedekindPrimePowerIndex K => i.2.1.val) h
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hPQ))

theorem normPrimeFiber_card (S : Finset Nat.Primes) :
    Fintype.card (NormPrimeFiber K S) =
      ∑ p ∈ S,((idealsOverPrime K p).filter (fun Q => Ideal.absNorm Q = (p : ℕ))).card := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  exact Finset.sum_attach S (fun p => ((idealsOverPrime K p).filter (fun Q => Ideal.absNorm Q = (p : ℕ))).card)

/-- Exact positivity comparison between finitely many actual norm-p fibers
and the full smoothed prime-ideal-power series. -/
theorem normPrimeFiber_log_count_le_smoothed
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ f) (hf : ∀ y : ℝ,0 ≤ (f y).re)
    (hmajor : ∀ y ∈ Icc (1 : ℝ) 2,1 ≤ (f y).re)
    (S : Finset Nat.Primes) {x : ℝ} (hx : 1 < x)
    (hS : ∀ p ∈ S,x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*x) :
    (Fintype.card (NormPrimeFiber K S) : ℝ)*Real.log x ≤
      (∑' i : DedekindPrimePowerIndex K,
        (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*f ((dedekindPrimePowerNorm K i : ℝ)/x)).re := by
  let a : DedekindPrimePowerIndex K → ℂ := fun i =>
    (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*f ((dedekindPrimePowerNorm K i : ℝ)/x)
  have hxpos : 0 < x := zero_lt_one.trans hx
  have ha : Summable a := (dedekindPrimePower_smoothed_hasSum K f hcompact hpositive hsmooth hxpos
    (σ := 2) (by norm_num)).summable
  have hn (i : DedekindPrimePowerIndex K) : 0 ≤ (a i).re := by
    dsimp [a]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    apply mul_nonneg _ (hf _)
    exact Real.log_nonneg (by exact_mod_cast (idealsOverPrime_norm_two_le K i.2.1.property).trans' (by norm_num : 1 ≤ 2))
  have hfirst (i : NormPrimeFiber K S) : Real.log x ≤ (a (normPrimeFiberEmbedding K S i)).re := by
    have hp := hS i.1.val i.1.property
    have hnorm := (Finset.mem_filter.mp i.2.property).2
    have hf1 : 1 ≤ (f ((i.1.val : ℝ)/x)).re := hmajor _ ⟨
      (le_div_iff₀ hxpos).mpr (by simpa using hp.1),
      (div_le_iff₀ hxpos).mpr hp.2⟩
    have hp0 : 0 < (i.1.val : ℝ) := hxpos.trans_le hp.1
    have hlog : Real.log x ≤ Real.log (i.1.val : ℝ) := Real.log_le_log hxpos hp.1
    have hlog0 : 0 ≤ Real.log (i.1.val : ℝ) := Real.log_nonneg (hx.le.trans hp.1)
    change Real.log x ≤ ((Real.log (Ideal.absNorm i.2.val) : ℂ)*
      f (((Ideal.absNorm i.2.val ^ (0+1) : ℕ) : ℝ)/x)).re
    simp only [zero_add,pow_one,hnorm,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact hlog.trans (by nlinarith)
  have hfinite : (∑ i : NormPrimeFiber K S,Real.log x) ≤
      ∑ i : NormPrimeFiber K S,(a (normPrimeFiberEmbedding K S i)).re :=
    Finset.sum_le_sum (fun i _ => hfirst i)
  have hsub : (∑ i : NormPrimeFiber K S,(a (normPrimeFiberEmbedding K S i)).re) ≤
      ∑' i : DedekindPrimePowerIndex K,(a i).re := by
    have H := (Complex.hasSum_re ha.hasSum).summable.sum_le_tsum (Finset.univ.map (normPrimeFiberEmbedding K S)) (fun i _ => hn i)
    simpa only [Finset.sum_map,Function.Embedding.coeFn_mk] using H
  calc
    _ = ∑ i : NormPrimeFiber K S,Real.log x := by simp [mul_comm]
    _ ≤ ∑' i : DedekindPrimePowerIndex K,(a i).re := hfinite.trans hsub
    _ = _ := (Complex.hasSum_re ha.hasSum).tsum_eq

end
end ArtinMatthews.VaryingKummerAnalytic
