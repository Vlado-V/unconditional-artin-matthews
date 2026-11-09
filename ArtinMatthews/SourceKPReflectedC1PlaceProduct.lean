module

public import ArtinMatthews.SourceKPReflectedC1CoverWords


set_option backward.privateInPublic true
@[expose] public section

/-! The actual residual coefficient separates finite cover words on
disjoint places. The local central coordinates remain in each word. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup StandardAdelic QuadraticWeil
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "F" => SourceKPFiniteAdeleCover K hζ
local notation "M" => sourceKPFiniteAdeleProjectiveMk K hζ
local notation "mk" => sourceFiniteKP2ProjectiveMk K hζ
local notation "prod" => sourceKPFiniteCoverPlaceProduct K hζ
local notation "emb" => sourceKPAdeleLocalCover K hζ
local notation "base" => sourceKPAdelicLocalBase K hζ

local notation "C₁" => sourceKPCuspResidualFourierValue K hζ (1 : Kˣ)

private theorem residual_placeProduct_of_local (U : Finset Pr) (qf : Gf)
    (hq : ∀ P ∈ U, base P (1,qf) = 1) (w : SourceKPFiniteCoverLocalWords K hζ)
    (W : Gf → ℂ) (V : Pr → ℂ)
    (hfac : ∀ P ∈ U, ∀ q : Gf, base P (1,q) = 1 →
      W (q * (sourceKPAdelicLocalProjective K hζ P (mk P (w P))).2) = W q * V P) :
    W (qf * M (prod U w)) = W qf * ∏ P ∈ U, V P := by
  induction U using Finset.induction_on with
  | empty =>
    change W (qf * M 1) = W qf * (∏ P ∈ (∅ : Finset Pr), V P)
    rw [map_one, mul_one, Finset.prod_empty, mul_one]
  | @insert P U hP ih =>
    let q := qf * M (prod U w)
    have hbase : base P (1,q) = 1 := by
      have he : ((1,q) : SourceKPAdelicProjective K hζ) =
          (1,qf) * (1,M (prod U w)) := Prod.ext (one_mul _).symm rfl
      rw [he, map_mul, hq P (Finset.mem_insert_self _ _),
        sourceKPFiniteCoverPlaceProduct_base_one K hζ U w P hP, mul_one]
    have hlast : prod ({P} : Finset Pr) w = emb P (w P) := by
      rw [show ({P} : Finset Pr) = insert P ∅ from rfl,
        sourceKPFiniteCoverPlaceProduct_insert K hζ ∅ w P (Finset.notMem_empty _)]
      exact mul_one _
    have he : qf * M (prod (insert P U) w) =
        q * (sourceKPAdelicLocalProjective K hζ P (mk P (w P))).2 := by
      rw [← Finset.union_singleton,
        sourceKPFiniteCoverPlaceProduct_union K hζ _ _ w (Finset.disjoint_singleton_right.mpr hP),
        hlast, map_mul, ← mul_assoc]
      rfl
    have hI : W q = W qf * ∏ Q ∈ U, V Q :=
      ih (fun Q hQ => hq Q (Finset.mem_insert_of_mem hQ))
        (fun Q hQ => hfac Q (Finset.mem_insert_of_mem hQ))
    rw [he, hfac P (Finset.mem_insert_self _ _) q hbase, hI, Finset.prod_insert hP]
    ac_rfl

theorem sourceKPCuspResidualFourierValue_placeProduct (S₀ : Finset Pr)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) {T : ℝ} (hT : 2 < T)
    (U : Finset (SourceExteriorPrime K S₀)) (qf : Gf) (hq : ∀ P ∈ U, base P.val (1,qf) = 1)
    (w : SourceKPFiniteCoverLocalWords K hζ) :
    C₁ (one_le_two.trans hT.le) (qf * M (prod (U.map (Function.Embedding.subtype (· ∉ sourceHilbertSet K S₀))) w)) =
      C₁ (one_le_two.trans hT.le) qf *
        ∏ P ∈ U, sourceKPTameCyclicWhittakerValue K hζ S₀ P hS (mk P.val (w P.val)) := by
  have hU (P : Pr) (hP : P ∈ U.map (Function.Embedding.subtype (· ∉ sourceHilbertSet K S₀))) : P ∉ sourceHilbertSet K S₀ := by
    obtain ⟨Q,_,rfl⟩ := Finset.mem_map.mp hP
    exact Q.property
  have hq' (P : Pr) (hP : P ∈ U.map (Function.Embedding.subtype (· ∉ sourceHilbertSet K S₀))) : base P (1,qf) = 1 := by
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_map.mp hP
    exact hq Q hQ
  let V (P : Pr) := if hP : P ∉ sourceHilbertSet K S₀ then
    sourceKPTameCyclicWhittakerValue K hζ S₀ ⟨P,hP⟩ hS (mk P (w P)) else 1
  have hfac (P : Pr) (hP : P ∈ U.map (Function.Embedding.subtype (· ∉ sourceHilbertSet K S₀)))
      (q : Gf) (hb : base P (1,q) = 1) :
      C₁ (one_le_two.trans hT.le) (q * (sourceKPAdelicLocalProjective K hζ P (mk P (w P))).2) =
        C₁ (one_le_two.trans hT.le) q * V P := by
    have hPS := hU P hP
    unfold V
    rw [dite_eq_left hPS]
    have hloc := sourceKPTameResidualFourierValue_factor K hζ S₀ ⟨P,hPS⟩ hS hT q hb (mk P (w P))
    simpa only [Subtype.coe_mk] using hloc
  rw [residual_placeProduct_of_local K hζ _ qf hq' w _ V hfac, Finset.prod_map]
  apply congrArg (C₁ (one_le_two.trans hT.le) qf * ·)
  apply Finset.prod_congr rfl
  intro P _
  exact dite_eq_left P.property

end
end ArtinMatthews
