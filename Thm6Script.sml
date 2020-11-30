open HolKernel Parse boolLib bossLib;

open ETCSaxiomTheory basicTheory;     

open Thm3Theory Thm5Theory;

     
val _ = new_theory "Thm6";

    

Theorem Thm6_first_sentence:
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ∧
            is_refl f0 f1 ∧ is_symm f0 f1 ∧ is_trans f0 f1 ∧
            is_mono ⟨f0, f1⟩ ∧
            (∀a0 a1. a0∶ one → A ∧ a1∶ one → A ∧
                     (coeqa f0 f1) o a0 = (coeqa f0 f1) o a1 ⇒
                     ∃r. r∶ one → R ∧ f0 o r = a0 ∧
                         f1 o r = a1) ⇒
            R ≅ eqo ((coeqa f0 f1) o p1 A A)
                    ((coeqa f0 f1) o p2 A A)
Proof
rw[] >> irule prop_2_corollary >>
qexistsl_tac [‘A × A’,
              ‘⟨f0,f1⟩’,
              ‘eqa (coeqa f0 f1 ∘ p1 A A)
                   (coeqa f0 f1 ∘ p2 A A)’]  >>
‘p1 A A∶ A× A → A ∧ p2 A A∶ A × A → A’
 by metis_tac[p1_hom,p2_hom] >>
‘coeqa f0 f1∶ A → coeqo f0 f1’ by metis_tac[coeqa_hom] >>
‘coeqa f0 f1 o p1 A A∶ (A × A) → coeqo f0 f1 ∧
 coeqa f0 f1 o p2 A A∶ (A × A) → coeqo f0 f1’
  by metis_tac[compose_hom] >>         
‘is_mono (eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A))’
 by metis_tac[eqa_is_mono] >>
‘eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A)∶
  eqo (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) →
  (A × A)’ by metis_tac[eqa_hom] >>
‘⟨f0,f1⟩∶ R → (A × A)’ by metis_tac[pa_hom] >> 
rw[] (* 2 *)
>- (qexists_tac ‘eq_induce (coeqa f0 f1 ∘ p1 A A)
                (coeqa f0 f1 ∘ p2 A A) (⟨f0,f1⟩ o x)’ >>
   ‘(coeqa f0 f1 ∘ p1 A A) ∘ ⟨f0,f1⟩ ∘ x =
   (coeqa f0 f1 ∘ p1 A A ∘ ⟨f0,f1⟩) ∘ x’
    by metis_tac[compose_assoc_4_3_2_left] >>
   ‘(coeqa f0 f1 ∘ p2 A A) ∘ ⟨f0,f1⟩ ∘ x =
    (coeqa f0 f1 ∘ p2 A A ∘ ⟨f0,f1⟩) ∘ x’
    by metis_tac[compose_assoc_4_3_2_left] >>
   ‘p1 A A ∘ ⟨f0,f1⟩ = f0 ∧
    p2 A A ∘ ⟨f0,f1⟩ = f1’ by metis_tac[p1_of_pa,p2_of_pa] >>
   ‘coeqa f0 f1 o f0 = coeqa f0 f1 o f1’
    by metis_tac[coeq_equlity] >>
   ‘eq_induce (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) (⟨f0,f1⟩ ∘ x)∶one →
        eqo (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A)’
     by (irule eq_induce_hom >>
        metis_tac[compose_hom]) >> rw[] >>
   ‘eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘
        eq_induce (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) (⟨f0,f1⟩ ∘ x) = ⟨f0,f1⟩ o x’
     suffices_by metis_tac[] >>
   irule eq_fac >>
   metis_tac[compose_hom])
>- (first_x_assum (qspecl_then
   [‘p1 A A o eqa (coeqa f0 f1 ∘ p1 A A)
                  (coeqa f0 f1 ∘ p2 A A) ∘ y’,
    ‘p2 A A o eqa (coeqa f0 f1 ∘ p1 A A)
                  (coeqa f0 f1 ∘ p2 A A) ∘ y’] assume_tac) >>
   ‘p2 A A ∘ eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘ y∶one → A ∧
    p1 A A ∘ eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘ y∶one → A’ by metis_tac[compose_hom] >>
   ‘coeqa f0 f1 ∘ p1 A A ∘
    eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘ y =
    (coeqa f0 f1 ∘ p1 A A ∘
    eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A)) ∘ y ∧
    coeqa f0 f1 ∘ p2 A A ∘
    eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘ y =
    (coeqa f0 f1 ∘ p2 A A ∘
    eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A)) ∘ y’
    by metis_tac[compose_assoc_4_3_left] >>
   ‘(coeqa f0 f1 ∘ p1 A A ∘
         eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A)) =
    (coeqa f0 f1 ∘ p2 A A ∘
         eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A))’
    by metis_tac[eq_equlity,compose_assoc] >>
   ‘∃r.r∶one → R ∧
        f0 ∘ r =
        p1 A A ∘ eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘ y ∧
        f1 ∘ r =
        p2 A A ∘ eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘ y’ by metis_tac[] >>
   qexists_tac ‘r’ >>
   ‘⟨f0,f1⟩ ∘ r∶ one → (A × A) ∧
    eqa (coeqa f0 f1 ∘ p1 A A)
        (coeqa f0 f1 ∘ p2 A A) ∘ y∶ one → (A × A)’
     by metis_tac[compose_hom] >>
   rw[] >>
   irule to_p_eq_applied >> qexistsl_tac [‘A’,‘A’,‘one’] >>
   simp[] >> metis_tac[compose_assoc,p1_of_pa,p2_of_pa])
QED

Theorem Thm6_lemma_3:
∀h R A. h∶ R → A ⇒
        ∃hb. hb∶ exp R (one + one) → exp A (one + one) ∧
             (∀psi. psi∶ R → one + one ⇒
                    ∀x. x∶ one → A ⇒
                        (ev A (one + one) o ⟨p1 A one, hb o tp (psi o p1 R one) o p2 A one⟩ o ⟨id A, to1 A⟩ o x = i2 one one ⇔
                         ∃r. r∶ one → R ∧
                             psi o r = i2 one one ∧
                             h o r = x))
Proof
rw[] >>
‘ev R two∶ (R × (exp R two)) → two’ by metis_tac[ev_hom] >>
qabbrev_tac ‘i₀ = i1 one one’ >>
qabbrev_tac ‘i₁ = i2 one one’ >>
‘i₀∶  one → two ∧ i₁∶ one → two’
 by (simp[Abbr‘i₀’,Abbr‘i₁’] >>
    metis_tac[i1_hom,i2_hom]) >>
‘to1 (R × (exp R two))∶ (R × (exp R two)) → one’
 by metis_tac[to1_hom] >>
‘i₁ o to1 (R × (exp R two))∶ (R × (exp R two)) → two’
 by metis_tac[compose_hom] >>
qabbrev_tac ‘t = i₁ o to1 (R × (exp R two))’ >>
(*maybe lemma about to true_A*)
qabbrev_tac ‘ψ = eqa (ev R two) t’ >>
qabbrev_tac ‘R' = eqo (ev R two) t’ >>
‘(p1 R (exp R two))∶ (R × (exp R two)) → R ∧
 (p2 R (exp R two))∶ (R × (exp R two)) → exp R two’
 by metis_tac[p1_hom,p2_hom] >>
‘h o (p1 R (exp R two))∶ (R × (exp R two)) → A’
 by metis_tac[compose_hom] >>
‘⟨h o (p1 R (exp R two)), p2 R (exp R two)⟩∶
 (R × (exp R two)) → (A × (exp R two))’ by metis_tac[pa_hom] >>
qabbrev_tac ‘h2R = ⟨h o (p1 R (exp R two)), p2 R (exp R two)⟩’>>
‘ψ∶ R' → (R × (exp R two))’
 by
  (simp[Abbr‘ψ’,Abbr‘R'’] >> metis_tac[eqa_hom]) >>
‘h2R o ψ∶ R' → (A × (exp R two))’ by metis_tac[compose_hom] >>
drule mono_epi_fac >> strip_tac >>
drule char_thm >> strip_tac >>
first_x_assum (qspecl_then [‘X’,‘A × exp R two’] assume_tac) >>
rename [‘m∶M → (A × exp R two)’] >>
qabbrev_tac ‘ϕ = char m’ >>
‘ϕ∶A × exp R two → two’ by simp[] >>
‘ ∀x.
    x∶one → (A × exp R two) ⇒
   ((∃x0. x0∶one → M ∧ m ∘ x0 = x) ⇔ ϕ ∘ x = i₁)’
   by (simp[Abbr‘i₁’] >> metis_tac[]) >>
Q.UNDISCH_THEN `m∶M → (A × exp R two) ⇒
        ϕ∶A × exp R two → one + one ∧
        ∀x.
            x∶one → (A × exp R two) ⇒
            ((∃x0. x0∶one → M ∧ m ∘ x0 = x) ⇔ ϕ ∘ x = i2 one one)` (K ALL_TAC) >>
‘tp ϕ∶ exp R two → exp A two’ by metis_tac[tp_hom] >>
qexists_tac ‘tp ϕ’ >> simp[] >> rw[] >>
‘ev A two∶ (A × (exp A two)) → two’ by metis_tac[ev_hom] >>
‘∀r. r∶ one → R ⇒ (psi o r = i₁ ⇔
                   ∃r'. r'∶ one → R' ∧
                        ψ o r' = ⟨r, tp (psi ∘ p1 R one)⟩)’
 by (rw[] >> simp[Abbr‘R'’,Abbr‘ψ’,Abbr‘t’,Abbr‘i₁’] >>
    metis_tac[mem_of_name_eqa]) >> 
simp[EQ_IMP_THM] >> rpt strip_tac (* 2 *) 
>- (‘ϕ o ⟨x, tp (psi ∘ p1 R one)⟩ =
    ev A two ∘ ⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 R one) o p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ x’ by metis_tac[compose_partial_ev] >> 
   (*need lemma*)
   (*use fact that epi has section*)
   ‘ϕ o ⟨x, tp (psi ∘ p1 R one)⟩ = i₁’ by metis_tac[] >>
   drule fac_char_via_any_map >> strip_tac >>
   first_x_assum (qspecl_then [‘h2R o ψ’,‘R'’,‘A × (exp R two)’,
                               ‘M’,‘m’,
                               ‘⟨x,tp (psi o p1 R one)⟩’]
                  assume_tac) >>
   ‘(psi ∘ p1 R one)∶ (R × one) → two’
    by metis_tac[compose_hom,p1_hom] >>
   ‘tp (psi ∘ p1 R one)∶ one → exp R two’
    by metis_tac[tp_hom] >>
   ‘⟨x,tp (psi ∘ p1 R one)⟩∶one → (A × exp R two)’
    by metis_tac[pa_hom] >> 
   ‘∃r'. r'∶one → R' ∧ (h2R ∘ ψ) ∘ r' = ⟨x,tp (psi ∘ p1 R one)⟩’
     by (first_x_assum irule >>
        metis_tac[Abbr‘ϕ’,Abbr‘i₁’]) >> 
   ‘(p1 R (exp R two)) o ψ o r'∶ one → R’
    by metis_tac[compose_hom] >>
   qexists_tac ‘(p1 R (exp R two)) o ψ o r'’ >>
   simp[] >> 
   rw[] (* 2 *)
   >- (qexists_tac ‘r'’ >> simp[] >>
      ‘psi o (p1 R one)∶ (R × one) → two’
       by metis_tac[compose_hom,p1_hom] >>
      ‘tp (psi ∘ p1 R one)∶ one → exp R two’
        by metis_tac[tp_hom] >>
      ‘p2 R (exp R two) o ψ ∘ r' =
       tp (psi ∘ p1 R one)’
      suffices_by
       (rw[] >> irule to_p_eq_applied >>
       ‘ψ o r'∶ one → (R × exp R two)’
        by metis_tac[compose_hom] >>
       ‘⟨p1 R (exp R two) ∘ ψ ∘ r',tp (psi ∘ p1 R one)⟩∶
        one → (R × exp R two)’
        by metis_tac[pa_hom] >> 
       qexistsl_tac [‘R’,‘exp R two’,‘one’] >>
       simp[] >>
       ‘tp (psi ∘ p1 R one) =
        p2 R (exp R two) ∘ ⟨p1 R (exp R two) ∘ ψ ∘ r',tp (psi ∘ p1 R one)⟩’ by metis_tac[p2_of_pa] >>
       simp[] >>
       metis_tac[p1_of_pa]) >>
      ‘p2 A (exp R two) o (h2R ∘ ψ) ∘ r' =
       p2 A (exp R two) o ⟨x,tp (psi ∘ p1 R one)⟩’
       by metis_tac[] >>
      ‘p2 A (exp R two) o ⟨x,tp (psi ∘ p1 R one)⟩ =
       tp (psi ∘ p1 R one)’ by metis_tac[p2_of_pa] >>
      ‘p2 R (exp R two) = p2 A (exp R two) o h2R’
        by (simp[Abbr‘h2R’] >> metis_tac[p2_of_pa]) >>
      simp[] >>
      ‘(p2 A (exp R two) ∘ h2R) ∘ ψ ∘ r' =
       p2 A (exp R two) ∘ (h2R ∘ ψ) ∘ r'’
       suffices_by metis_tac[] >>
      irule compose_assoc_4_2_left_middle >>
            metis_tac[p2_hom])
   >- (‘p1 A (exp R two) o  (h2R ∘ ψ) ∘ r' = x’
        by (simp[] >> metis_tac[p1_of_pa]) >>
      ‘p1 A (exp R two) ∘ h2R = h ∘ p1 R (exp R two)’
       by (simp[Abbr‘h2R’] >> metis_tac[p1_of_pa]) >>
      ‘p1 A (exp R two) ∘ (h2R ∘ ψ) ∘ r' =
       (p1 A (exp R two) ∘ h2R) ∘ ψ ∘ r'’
       by metis_tac[compose_assoc_4_2_left_middle,p1_hom] >>
      ‘(p1 A (exp R two) ∘ h2R) ∘ ψ ∘ r' = x’
       by metis_tac[] >>
      ‘(h ∘ p1 R (exp R two)) ∘ ψ ∘ r' = x’
       by metis_tac[] >>
      metis_tac[compose_assoc_4_2_left,p1_hom]))
>- (‘ev A two ∘ ⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 R one) o p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ x = ϕ o ⟨x, tp (psi ∘ p1 R one)⟩’ by
    metis_tac[compose_partial_ev] >>
   simp[SimpLHS] >>
   ‘∃r'. r'∶one → R' ∧ ψ ∘ r' = ⟨r, tp (psi ∘ p1 R one)⟩’
    by metis_tac[] >>
   Q.UNDISCH_THEN
   ‘∀r.  r∶one → R ⇒
            (psi ∘ r = i₁ ⇔
             ∃r'. r'∶one → R' ∧ ψ ∘ r' = ⟨r,tp (psi ∘ p1 R one)⟩)’ (K ALL_TAC) >>
   ‘(h2R o ψ) ∘ r' = h2R o ⟨r, tp (psi ∘ p1 R one)⟩’
    by metis_tac[compose_assoc] >>
   ‘m o e o r' = h2R ∘ ⟨r, tp (psi ∘ p1 R one)⟩’
    by metis_tac[compose_assoc] >>
   ‘(psi ∘ p1 R one)∶ (R × one) → two’
    by metis_tac[compose_hom,p1_hom] >>
   ‘tp (psi ∘ p1 R one)∶ one → exp R two’
    by metis_tac[tp_hom] >>
   ‘⟨x,tp (psi ∘ p1 R one)⟩∶one → (A × exp R two)’
    by metis_tac[pa_hom] >> 
   ‘h2R ∘ ⟨r,tp (psi ∘ p1 R one)⟩ =⟨x, tp (psi ∘ p1 R one)⟩’
    by
     (irule to_p_eq_applied >>
     qexistsl_tac [‘A’,‘exp R two’,‘one’] >>
     simp[] >>
     ‘⟨r,tp (psi ∘ p1 R one)⟩∶ one → (R × exp R two)’
      by metis_tac[pa_hom] >>
     ‘h2R ∘ ⟨r,tp (psi ∘ p1 R one)⟩∶one → (A × exp R two)’
      by metis_tac[compose_hom] >>
     simp[] >>
     simp[Abbr‘h2R’] >>
     ‘p2 A (exp R two) ∘ ⟨x,tp (psi ∘ p1 R one)⟩ =
      tp (psi ∘ p1 R one)’ by metis_tac[p2_of_pa] >>
     ‘p1 A (exp R two) ∘ ⟨x,tp (psi ∘ p1 R one)⟩ = x’
      by metis_tac[p1_of_pa] >>
     simp[] >>
     ‘⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩∶
      (R × (exp R two)) → (A × (exp R two))’
      by metis_tac[compose_hom,pa_hom] >>
     ‘p1 A (exp R two) ∘ ⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩ ∘ ⟨r,tp (psi ∘ p1 R one)⟩ =
      (p1 A (exp R two) ∘ ⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩) ∘ ⟨r,tp (psi ∘ p1 R one)⟩’
      by metis_tac[p1_hom,compose_assoc] >>
     ‘p2 A (exp R two) ∘ ⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩ ∘ ⟨r,tp (psi ∘ p1 R one)⟩ =
      (p2 A (exp R two) ∘ ⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩) ∘ ⟨r,tp (psi ∘ p1 R one)⟩’
      by metis_tac[p2_hom,compose_assoc] >>
     simp[] >>
     ‘p1 A (exp R two) ∘ ⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩ = h ∘ p1 R (exp R two)’ by metis_tac[compose_hom,p1_of_pa] >>
     ‘p2 A (exp R two) ∘ ⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩ = p2 R (exp R two)’ by metis_tac[compose_hom,p2_of_pa] >>
     simp[] >>
     ‘p2 R (exp R two) ∘ ⟨r,tp (psi ∘ p1 R one)⟩ =
      tp (psi ∘ p1 R one)’ by metis_tac[p2_of_pa] >>
     simp[] >>
     ‘(h ∘ p1 R (exp R two)) ∘ ⟨r,tp (psi ∘ p1 R one)⟩ =
      h ∘ p1 R (exp R two) ∘ ⟨r,tp (psi ∘ p1 R one)⟩’
      by metis_tac[compose_assoc] >>
     simp[] >>
     ‘p1 R (exp R two) ∘ ⟨r,tp (psi ∘ p1 R one)⟩ = r’
      by metis_tac[p1_of_pa] >>
     metis_tac[]) >>
   ‘ϕ ∘ h2R ∘ ⟨r,tp (psi ∘ p1 R one)⟩ = i₁’
    by (simp[Abbr‘ϕ’,Abbr‘i₁’] >>
       drule fac_char >> strip_tac >>
       first_x_assum (qspecl_then [‘M’,‘(A × exp R two)’,‘one’,‘⟨x,tp (psi ∘ p1 R one)⟩’,‘e o r'’] assume_tac) >>
       ‘to1 one = id one’ by metis_tac[to1_unique,id1,to1_hom]>>
       ‘i2 one one = i2 one one o id one’
        by metis_tac[idR] >>
       ‘char m ∘ ⟨x,tp (psi ∘ p1 R one)⟩ = i2 one one o to1 one’
        suffices_by metis_tac[] >>
       first_x_assum irule >> rw[] >>
       metis_tac[compose_hom,pa_hom]) >>
       metis_tac[])
(*
     cheat >>
   ‘h2R ∘ ⟨r,tp (psi ∘ p2 one R)⟩ = ⟨x,tp (psi ∘ p2 one R)⟩’
    by cheat >>
   metis_tac[]
   (*use fac_char*)*)
  
QED


Theorem bar_exists:
∀h.  ∃hb. hb∶ exp (dom h) (one + one) → exp (cod h) (one + one) ∧
             (∀psi. psi∶ (dom h) → one + one ⇒
                    ∀x. x∶ one → (cod h) ⇒
                        (ev (cod h) (one + one) o ⟨p1 (cod h) one, hb o tp (psi o p1 (dom h) one) o p2 (cod h) one⟩ o ⟨id (cod h), to1 (cod h)⟩ o x = i2 one one ⇔
                         ∃r. r∶ one → (dom h) ∧
                             psi o r = i2 one one ∧
                             h o r = x))
Proof
rw[] >>
qabbrev_tac ‘R = dom h’ >>
qabbrev_tac ‘A = cod h’ >>
‘h∶ R → A’ by metis_tac[hom_def] >>
drule Thm6_lemma_3 >> rw[]
QED   


Theorem diag_is_mono:
∀A. is_mono ⟨id A,id A⟩
Proof
rw[] >> ‘⟨id A,id A⟩∶ A → (A × A)’ by metis_tac[id1,pa_hom] >>
irule is_mono_applied >> qexistsl_tac [‘A’,‘A × A’] >> rw[] >>
‘p1 A A o ⟨id A,id A⟩ ∘ f = p1 A A o ⟨id A,id A⟩ ∘ g’
 by metis_tac[] >>
‘p1 A A ∘ ⟨id A,id A⟩ ∘ f =  (p1 A A ∘ ⟨id A,id A⟩) ∘ f ∧
 p1 A A ∘ ⟨id A,id A⟩ ∘ g =  (p1 A A ∘ ⟨id A,id A⟩) ∘ g’
 by metis_tac[p1_hom,compose_assoc] >>
metis_tac[p1_of_pa,idL,id1]
QED

Theorem fac_diag_eq:
∀x0 x y A. x∶ one → A ∧ y∶ one → A ∧ x0∶ one → A ∧
         ⟨id A,id A⟩ ∘ x0 = ⟨y,x⟩ ⇒
         y = x
Proof
rw[] >>
‘p1 A A∶ (A × A) → A ∧ p2 A A∶ (A × A) → A’
 by metis_tac[p1_hom,p2_hom] >>
‘⟨id A,id A⟩∶ A → (A × A)’ by metis_tac[id1,pa_hom] >>
‘p1 A A o ⟨id A,id A⟩ ∘ x0 = p1 A A o ⟨y,x⟩ ∧
 p2 A A o ⟨id A,id A⟩ ∘ x0 = p2 A A o ⟨y,x⟩’ by metis_tac[] >>
‘p1 A A o ⟨y,x⟩ = y ∧ p2 A A o ⟨y,x⟩ = x’
 by metis_tac[p1_of_pa,p2_of_pa] >>
simp[] >>
‘p1 A A ∘ ⟨id A,id A⟩ ∘ x0 =
 p2 A A ∘ ⟨id A,id A⟩ ∘ x0’ suffices_by metis_tac[] >>
‘p1 A A ∘ ⟨id A,id A⟩ =
 p2 A A ∘ ⟨id A,id A⟩’ suffices_by metis_tac[compose_assoc] >>
metis_tac[id1,p1_of_pa,p2_of_pa]
QED        
                 


Theorem Thm6_lemma_2:
∀A. ∃sg. sg∶ A → exp A (one + one) ∧
    ∀x y. x∶ one → A ∧ y∶ one → A ⇒
          (ev A (one + one) o ⟨p1 A one, sg o x o p2 A one⟩ o ⟨id A, to1 A⟩ o y =
           i2 one one ⇔ y = x)
Proof
rw[] >>
qexists_tac ‘tp (char ⟨id A,id A⟩)’ >>
‘is_mono ⟨id A,id A⟩’ by metis_tac[diag_is_mono] >>
drule char_thm >> strip_tac >>
‘⟨id A,id A⟩∶ A → (A × A)’ by metis_tac[id1,pa_hom] >>
first_x_assum drule >> strip_tac >>
‘tp (char ⟨id A,id A⟩)∶A → exp A (one + one)’
 by metis_tac[tp_hom] >>
simp[] >> rw[] >>
‘⟨p1 A one,tp (char ⟨id A,id A⟩) ∘ x o p2 A one⟩ =
 ⟨p1 A A,tp (char ⟨id A,id A⟩) o p2 A A⟩ o ⟨p1 A one, x o p2 A one⟩’
 by (irule parallel_p_one_side >> metis_tac[]) >>
rw[] >>
‘⟨p1 A one,x ∘ p2 A one⟩∶ (A × one) → (A × A)’
 by metis_tac[compose_hom,p1_hom,p2_hom,pa_hom] >>
‘⟨id A,to1 A⟩∶ A → (A × one)’ by metis_tac[id1,to1_hom,pa_hom]>>
‘ev A (one + one) ∶ (A × (exp A (one + one))) → (one+ one)’
 by metis_tac[ev_hom] >>
‘⟨p1 A A,tp (char ⟨id A,id A⟩) ∘ p2 A A⟩∶
 (A × A) → (A × (exp A (one + one)))’
 by metis_tac[p1_hom,p2_hom,compose_hom,pa_hom]>>
‘ev A (one + one) ∘
        (⟨p1 A A,tp (char ⟨id A,id A⟩) ∘ p2 A A⟩ ∘ ⟨p1 A one,x ∘ p2 A one⟩) ∘
        ⟨id A,to1 A⟩ ∘ y =
 (ev A (one + one) ∘
        ⟨p1 A A,tp (char ⟨id A,id A⟩) ∘ p2 A A⟩) ∘ ⟨p1 A one,x ∘ p2 A one⟩ ∘
        ⟨id A,to1 A⟩ ∘ y’
 by metis_tac[compose_assoc_5_2_left1_left] >>
rw[] >>
‘(ev A (one + one) ∘ ⟨p1 A A,tp (char ⟨id A,id A⟩) ∘ p2 A A⟩) =
 char ⟨id A,id A⟩’
 by metis_tac[ev_of_tp] >>
rw[] >>
‘⟨y,x⟩∶ one → (A × A)’ by metis_tac[pa_hom] >>
‘⟨p1 A one,x ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ y∶ one → (A × A)’
 by metis_tac[compose_hom] >>
‘⟨p1 A one,x ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ y =
 ⟨y,x⟩’
 by  (drule to_p_eq_applied >> rw[] >> first_x_assum irule >>
     simp[] >>
     ‘(p1 A A) o ⟨y,x⟩ = y ∧ (p2 A A) o ⟨y,x⟩ = x’
      by metis_tac[p1_of_pa,p2_of_pa] >>
     simp[] >>
     ‘p1 A A ∘ ⟨p1 A one,x ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ y =
      (p1 A A ∘ ⟨p1 A one,x ∘ p2 A one⟩) ∘ ⟨id A,to1 A⟩ ∘ y ∧
      p2 A A ∘ ⟨p1 A one,x ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ y =
      (p2 A A ∘ ⟨p1 A one,x ∘ p2 A one⟩) ∘ ⟨id A,to1 A⟩ ∘ y’
      by metis_tac[p1_hom,p2_hom,compose_assoc_4_2_left] >>
     simp[] >>
     ‘(p1 A A ∘ ⟨p1 A one,x ∘ p2 A one⟩) = p1 A one ∧
      (p2 A A ∘ ⟨p1 A one,x ∘ p2 A one⟩) = x o p2 A one’
      by metis_tac[compose_hom,p1_hom,p2_hom,
                   p1_of_pa,p2_of_pa]>>
     simp[] >>
     ‘p1 A one o ⟨id A, to1 A⟩ o y =
      (p1 A one o ⟨id A, to1 A⟩) o y ∧
     (x ∘ p2 A one) ∘ ⟨id A,to1 A⟩ ∘ y =
     ((x ∘ p2 A one) ∘ ⟨id A,to1 A⟩) ∘ y’
      by metis_tac[compose_hom,compose_assoc,p1_hom,p2_hom] >>
     simp[] >>
     ‘p1 A one o ⟨id A, to1 A⟩ = id A’
      by metis_tac[p1_of_pa,id1,to1_hom] >>
     ‘(x ∘ p2 A one) ∘ ⟨id A,to1 A⟩ =
      x ∘ p2 A one ∘ ⟨id A,to1 A⟩’
      by metis_tac[p2_hom,compose_assoc,id1,to1_hom,pa_hom] >>
     simp[] >>
     ‘p2 A one ∘ ⟨id A,to1 A⟩ = to1 A’
      by metis_tac[p2_hom,id1,to1_hom,p2_of_pa] >>
     simp[] >> 
     ‘(x ∘ to1 A) ∘ y = x ∘ to1 A ∘ y’
      by metis_tac[to1_hom,compose_assoc] >>
     ‘to1 A o y = id one’
      by (irule to1_unique >>
         metis_tac[compose_hom,to1_hom,id1]) >>
     simp[] >>
     metis_tac[idL,idR]) >>
simp[] >> first_x_assum (qspec_then ‘⟨y,x⟩’ assume_tac) >>
first_x_assum drule >> rw[] >>
‘(∃x0. x0∶one → A ∧ ⟨id A,id A⟩ ∘ x0 = ⟨y,x⟩) ⇔ y = x’
 suffices_by metis_tac[] >>
Q.UNDISCH_THEN
  ‘(∃x0. x0∶one → A ∧ ⟨id A,id A⟩ ∘ x0 = ⟨y,x⟩) ⇔
   char ⟨id A,id A⟩ ∘ ⟨y,x⟩ = i2 one one’ (K ALL_TAC) >>
simp[] >>
rw[EQ_IMP_THM]
>- metis_tac[fac_diag_eq] >>
qexists_tac ‘x’ >> rw[] >>
drule to_p_eq_applied >> rw[] >>
‘⟨x,x⟩ = ⟨id A,id A⟩ ∘ x’
 suffices_by metis_tac[] >>
first_x_assum irule >> rw[] (* 3 *)
>- (‘p1 A A ∘ ⟨id A,id A⟩ ∘ x = (p1 A A ∘ ⟨id A,id A⟩) ∘ x’
     by metis_tac[compose_assoc,p1_hom] >>
   simp[] >> metis_tac[p1_of_pa,idL,id1])
>- metis_tac[p2_of_pa,idL,id1,compose_assoc,p2_hom]
>- metis_tac[compose_hom] 
QED



Theorem sg_exists_thm = SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] Thm6_lemma_2        

val sg_def = new_specification ("sg_def",["sg"],sg_exists_thm)        


Theorem bar_exists_thm = SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] bar_exists  

val bar_def = new_specification ("bar_def",["bar"],bar_exists_thm)


Theorem bar_thm:
∀h R A. h∶ R → A ⇒
         bar h∶exp R two → exp A two ∧
         ∀psi.
             psi∶ R → two ⇒
             ∀x.
                 x∶one → A ⇒
                 (ev A two ∘
                  ⟨p1 A one,bar h ∘ tp (psi ∘ p1 R one) ∘
                  p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ x =
                  i2 one one ⇔
                  ∃r. r∶one → R ∧ psi ∘ r = i2 one one ∧ h ∘ r = x)
Proof
strip_tac >> strip_tac >> strip_tac >> strip_tac >>
‘dom h = R ∧ cod h = A’ by metis_tac[hom_def] >>
metis_tac[bar_def]
QED
   
        
Theorem Thm6_g_ev:
∀a a' f0 f1 R A.
 a∶ one → A ∧ a'∶ one → A ∧ f0∶ R → A ∧ f1∶ R → A ⇒
 (ev A two o
 ⟨p1 A one,
  bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a o p2 A one⟩ o ⟨id A,to1 A⟩ o
 a' = i2 one one ⇔
 (∃r. r∶ one → R ∧ f0 o r = a ∧ f1 o r = a'))
Proof 
rw[] >> drule bar_thm >> rw[] >>
(*needed*) 
‘ev A two∶ (A × exp A two) → two’ by metis_tac[ev_hom] >>
‘p1 A one ∶ (A × one) → A’ by metis_tac[p1_hom] >>
‘id A∶ A → A’ by metis_tac[id1] >>
‘to1 A∶ A → one’ by metis_tac[to1_hom] >> 
‘sg A∶ A → exp A two’ by metis_tac[sg_def] >>
‘p2 A one∶ (A × one) → one’ by metis_tac[p2_hom] >>
‘⟨id A, to1 A⟩∶ A→ (A × one)’ by metis_tac[pa_hom] >>
‘a ∘ p2 A one∶ (A × one) → A’ by metis_tac[compose_hom] >>
‘sg A ∘ a ∘ p2 A one∶ (A × one) → exp A two’
 by metis_tac[compose_hom] >>
‘⟨p1 A one,sg A ∘ a ∘ p2 A one⟩∶ (A × one) → (A × exp A two)’
 by metis_tac[pa_hom] >>
‘ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 ∶ R → two’ by metis_tac[compose_hom] >>
qabbrev_tac ‘psi = ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0’ >>
‘psi o p1 R one∶ (R × one) → two’ by metis_tac[compose_hom,p1_hom] >>
‘tp (psi o p1 R one)∶ one → exp R two’ by metis_tac[tp_hom] >>
‘sg A o a∶ one → exp A two’ by metis_tac[compose_hom] >>
‘p1 R (exp A two)∶ (R × exp A two) → R ∧
 p2 R (exp A two)∶ (R × exp A two) → exp A two’
 by metis_tac[p1_hom,p2_hom] >>
‘f0 ∘ p1 R (exp A two)∶ (R × exp A two) → A’
 by metis_tac[compose_hom] >>
‘⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩∶
 (R × exp A two) → (A × (exp A two))’ by metis_tac[pa_hom] >>
‘ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩∶
 (R × exp A two) → two’ by metis_tac[compose_hom] >>
‘tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩)∶
 exp A two → exp R two’ by metis_tac[tp_hom] >>
‘tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a∶
 one → exp R two’ by metis_tac[compose_hom] >>
‘ev R two∶ (R × exp R two) → two’ by metis_tac[ev_hom] >>
‘⟨p1 R (exp A two),tp
          (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
        p2 R (exp A two)⟩∶ (R × exp A two) → (R × exp R two)’
  by metis_tac[compose_hom,pa_hom] >>
‘p1 R A∶ (R × A) → R ∧ p2 R A∶ (R × A) → A’
 by metis_tac[p1_hom,p2_hom] >>
‘⟨p1 R A,sg A ∘ p2 R A⟩∶ (R × A) → (R × exp A two)’
 by metis_tac[compose_hom,pa_hom] >>
‘p1 R one∶ (R × one) → R ∧ p2 R one∶ (R × one) → one’
 by metis_tac[p1_hom,p2_hom] >>
‘⟨p1 R one,a ∘ p2 R one⟩∶ (R × one) → (R × A)’
 by metis_tac[compose_hom,pa_hom] >>
‘tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a = tp (psi ∘ p1 R one)’
 by (irule ev_eq_eq >> qexistsl_tac [‘R’,‘two’,‘one’] >> simp[] >>
    ‘ev R two ∘ ⟨p1 R one,tp (psi ∘ p1 R one) ∘ p2 R one⟩ =
     psi ∘ p1 R one’ by metis_tac[ev_of_tp] >>
    simp[Abbr‘psi’] >>
    ‘⟨p1 R one,(tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a) ∘ p2 R one⟩ =
     ⟨p1 R (exp A two), tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) o p2 R (exp A two)⟩ o
     ⟨p1 R A, sg A o p2 R A⟩ o
     ⟨p1 R one, a o p2 R one⟩’
     by (irule parallel_p_one_side_three >> metis_tac[]) >>
    simp[] >>
    ‘ev R two ∘
        ⟨p1 R (exp A two),tp
          (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
        p2 R (exp A two)⟩ ∘ ⟨p1 R A,sg A ∘ p2 R A⟩ ∘ ⟨p1 R one,a ∘ p2 R one⟩ =
     (ev R two ∘
     ⟨p1 R (exp A two),tp
      (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
     p2 R (exp A two)⟩) ∘ ⟨p1 R A,sg A ∘ p2 R A⟩ ∘ ⟨p1 R one,a ∘ p2 R one⟩’ by metis_tac[compose_assoc_4_2_left] >>
    simp[] >>
    ‘ev R two ∘
         ⟨p1 R (exp A two),tp
           (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
         p2 R (exp A two)⟩ =
     ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩’
      by metis_tac[ev_of_tp] >>
    simp[] >>
    ‘(ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
        ⟨p1 R A,sg A ∘ p2 R A⟩ ∘ ⟨p1 R one,a ∘ p2 R one⟩ =
     ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩ ∘
        ⟨p1 R A,sg A ∘ p2 R A⟩ ∘ ⟨p1 R one,a ∘ p2 R one⟩’
     by (irule compose_assoc_4_2_left >> metis_tac[]) >>
    simp[] >>
    ‘(ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0) ∘
        p1 R one =
     ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 ∘
        p1 R one’
      by (irule compose_assoc_5_4_left_SYM >> metis_tac[]) >>
    simp[] >>
    ‘⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩ ∘
        ⟨p1 R A,sg A ∘ p2 R A⟩ ∘ ⟨p1 R one,a ∘ p2 R one⟩ =
     ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 ∘
        p1 R one’ suffices_by metis_tac[] >>
    irule to_p_eq_applied >>
    ‘⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 ∘ p1 R one∶
     (R × one) → (A × exp A two)’ by metis_tac[compose_hom] >>
    ‘⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩ ∘
     ⟨p1 R A,sg A ∘ p2 R A⟩ ∘ ⟨p1 R one,a ∘ p2 R one⟩∶
     (R × one) → (A × exp A two)’
     by metis_tac[compose_hom] >>
    qexistsl_tac [‘A’,‘exp A two’,‘(R × one)’] >> simp[] >>
    ‘sg A ∘ a ∘ p2 A one∶ (A × one) → exp A two’
     by metis_tac[compose_hom] >> 
    rw[] (* 2 *)
    >- (‘p1 A (exp A two) ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 ∘ p1 R one =
        (p1 A (exp A two) ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩) ∘ ⟨id A,to1 A⟩ ∘ f0 ∘ p1 R one’
         by (irule compose_assoc_5_2_left_SYM >>
            metis_tac[p1_hom,p2_hom,compose_hom,pa_hom]) >>
       simp[] >>
       ‘(p1 A (exp A two) ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩) =
        p1 A one’ by metis_tac[p1_of_pa] >>
       simp[] >>
       ‘p1 A one ∘ ⟨id A,to1 A⟩ o f0 ∘ p1 R one =
        (p1 A one ∘ ⟨id A,to1 A⟩) o f0 ∘ p1 R one’
        by metis_tac[compose_assoc_4_2_left] >>
       simp[] >>
       ‘p1 A one ∘ ⟨id A,to1 A⟩ = id A’
        by metis_tac[p1_of_pa] >>
       simp[] >>
       ‘id A ∘ f0 ∘ p1 R one = f0 ∘ p1 R one’
        by metis_tac[idL,compose_hom] >> simp[] >>
       ‘p1 A (exp A two) ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩ ∘
        ⟨p1 R A,sg A ∘ p2 R A⟩ ∘ ⟨p1 R one,a ∘ p2 R one⟩ =
       (p1 A (exp A two) ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
        ⟨p1 R A,sg A ∘ p2 R A⟩ ∘ ⟨p1 R one,a ∘ p2 R one⟩’
        by (irule compose_assoc_4_2_left_SYM >> metis_tac[p1_hom])>>
       simp[] >>
       ‘p1 A (exp A two) ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩ =
       f0 ∘ p1 R (exp A two)’ by metis_tac[p1_of_pa] >>
       simp[] >>
       ‘(f0 ∘ p1 R (exp A two)) ∘ ⟨p1 R A,sg A ∘ p2 R A⟩ ∘
        ⟨p1 R one,a ∘ p2 R one⟩ =
        f0 ∘ p1 R (exp A two) ∘ ⟨p1 R A,sg A ∘ p2 R A⟩ ∘
        ⟨p1 R one,a ∘ p2 R one⟩’
        by (irule compose_assoc_4_2_left >> metis_tac[]) >>
       simp[] >>
       ‘f0 ∘ p1 R (exp A two) ∘ ⟨p1 R A,sg A ∘ p2 R A⟩ ∘
        ⟨p1 R one,a ∘ p2 R one⟩ =
        f0 ∘ (p1 R (exp A two) ∘ ⟨p1 R A,sg A ∘ p2 R A⟩) ∘
        ⟨p1 R one,a ∘ p2 R one⟩’
        by (irule compose_assoc_4_2_middle_SYM >> metis_tac[]) >>
       ‘p1 R (exp A two) ∘ ⟨p1 R A,sg A ∘ p2 R A⟩ = p1 R A’
        by (irule p1_of_pa >> metis_tac[compose_hom]) >>
       simp[] >>
       ‘p1 R A ∘ ⟨p1 R one,a ∘ p2 R one⟩ = p1 R one’
        by (irule p1_of_pa >> metis_tac[p1_hom,p2_hom,compose_hom]) >>
       metis_tac[])
    >- (‘p2 A (exp A two) ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 ∘ p1 R one =
        (p2 A (exp A two) ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩) ∘ ⟨id A,to1 A⟩ ∘ f0 ∘ p1 R one’
         by (irule compose_assoc_4_2_left_SYM >>
            metis_tac[compose_hom,pa_hom,p1_hom,p2_hom]) >>
       ‘p2 A (exp A two) ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ =
        sg A ∘ a ∘ p2 A one’
        by metis_tac[p2_of_pa] >>
       simp[] >>
       ‘(sg A ∘ a ∘ p2 A one) ∘ ⟨id A,to1 A⟩ ∘ f0 ∘ p1 R one =
        sg A ∘ a ∘ (p2 A one ∘ ⟨id A,to1 A⟩) ∘ f0 ∘ p1 R one’
        by (irule compose_assoc_6_3_2_left_middle >>
           metis_tac[]) >>
       simp[] >>
       ‘p2 A one ∘ ⟨id A,to1 A⟩ = to1 A’
        by metis_tac[p2_of_pa] >>
       simp[] >>
       ‘p2 A (exp A two) ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩ ∘
        ⟨p1 R A,sg A ∘ p2 R A⟩ ∘ ⟨p1 R one,a ∘ p2 R one⟩ =
        (p2 A (exp A two) ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ ⟨p1 R A,sg A ∘ p2 R A⟩ ∘ ⟨p1 R one,a ∘ p2 R one⟩’
        by (irule compose_assoc_4_2_left_SYM >>
           metis_tac[compose_hom,pa_hom,p1_hom,p2_hom]) >>
       ‘p2 A (exp A two) ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩ =
        p2 R (exp A two)’
        by metis_tac[p2_of_pa] >>
       simp[] >>
       ‘p2 R (exp A two) ∘ ⟨p1 R A,sg A ∘ p2 R A⟩ ∘ ⟨p1 R one,a ∘ p2 R one⟩ =
       (p2 R (exp A two) ∘ ⟨p1 R A,sg A ∘ p2 R A⟩) ∘ ⟨p1 R one,a ∘ p2 R one⟩’ by metis_tac[compose_assoc] >>
       ‘p2 R (exp A two) ∘ ⟨p1 R A,sg A ∘ p2 R A⟩ = sg A ∘ p2 R A’
        by metis_tac[p2_of_pa,compose_hom,p1_hom,p2_hom] >>
       simp[] >>
       ‘(sg A ∘ p2 R A) ∘ ⟨p1 R one,a ∘ p2 R one⟩ =
        sg A ∘ p2 R A ∘ ⟨p1 R one,a ∘ p2 R one⟩’
        by metis_tac[compose_assoc] >>
       ‘p2 R A ∘ ⟨p1 R one,a ∘ p2 R one⟩ = a ∘ p2 R one’
        by metis_tac[p2_of_pa,compose_hom,p1_hom,p2_hom] >>
       simp[] >>
       ‘p2 R one = to1 A ∘ f0 ∘ p1 R one’
        by (irule to1_unique >> metis_tac[compose_hom]) >>
       metis_tac[])) >>
          
(*     
‘∃psi. psi∶ R → two ∧
       tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a = tp (psi ∘ p1 R one) ’ by cheat >>
*)

       
simp[] >>
‘bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a ∘
        p2 A one =
 bar f1 ∘
        (tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a) ∘
        p2 A one’
  by
   (‘tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
        sg A ∘ a ∘ p2 A one =
    (tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a) ∘ p2 A one’ suffices_by metis_tac[] >>
   metis_tac[compose_assoc_4_3_left]) >>
simp[] >>
‘∀r. r∶ one → R ⇒ (f0 o r = a ⇔ psi o r = i2 one one)’
 suffices_by metis_tac[] >>
rw[] >>(*
‘psi = ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0’ by cheat need a lemma about psi*)
simp[Abbr‘psi’] >>
‘(ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 o r =
              i2 one one ⇔ f0 o r = a)’
 by (irule (sg_def |> SPEC_ALL |> CONJUNCT2) >>
    metis_tac[compose_hom]) >>
‘ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 ∘ r =
 (ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0) ∘ r’ suffices_by metis_tac[] >>
irule compose_assoc_5_4_left >> metis_tac[]
(*smart way for such matching?*)
QED

Theorem Thm6_g_ev':
∀a a' f0 f1 R A.
         a∶one → A ∧ a'∶one → A ∧ f0∶R → A ∧ f1∶R → A ⇒
         (ev A two ∘
          ⟨p1 A one,bar f1 ∘
          tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
          a ∘ p2 A one⟩ ∘ ⟨a',id one⟩ =
          i2 one one ⇔ ∃r. r∶one → R ∧ f0 ∘ r = a ∧ f1 ∘ r = a')
Proof 
rw[] >>
‘(ev A two ∘
          ⟨p1 A one,bar f1 ∘
          tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
          a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ a' =
          i2 one one ⇔ ∃r. r∶one → R ∧ f0 ∘ r = a ∧ f1 ∘ r = a')’
  by (irule Thm6_g_ev  >> rw[]) >>
‘⟨id A,to1 A⟩ ∘ a' = ⟨a',id one⟩’ suffices_by metis_tac[] >>
metis_tac[compose_with_id_to1]
QED

        
Theorem f0g_eq_f1g:
∀f0 f1 R A.
 f0∶ R → A ∧ f1∶ R → A ∧ is_symm f0 f1 ∧ is_trans f0 f1 ⇒
 (bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A) o f0 =
 (bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A) o f1
Proof
rw[] >> 
irule fun_ext >>
qexistsl_tac [‘R’,‘exp A two’] >>
‘bar f1∶ exp R two → exp A two’ by metis_tac[bar_thm] >>
‘p1 R (exp A two)∶ (R × exp A two) → R ∧
 p2 R (exp A two)∶ (R × exp A two) → exp A two’
 by metis_tac[p1_hom,p2_hom] >>
‘f0 ∘ p1 R (exp A two)∶ (R × exp A two) → A’
 by metis_tac[compose_hom] >>
‘⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩∶
 (R × exp A two) → (A × exp A two)’
 by metis_tac[pa_hom] >>
‘ev A two∶ (A × exp A two) → two’ by metis_tac[ev_hom] >>
‘ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩∶
 (R × exp A two) → two’ by metis_tac[compose_hom] >>
‘tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩)∶
 exp A two → exp R two’ by metis_tac[tp_hom] >>
‘sg A ∶ A → exp A two’ by metis_tac[sg_def] >>
‘(bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
         sg A) ∘ f0∶R →
        exp A two ∧
        (bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
         sg A) ∘ f1∶R →
        exp A two’ by metis_tac[compose_hom] >>
simp[] >> rw[] >>
rename [‘r∶ one → R’] >>
‘((bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
          sg A) ∘ f0) ∘ r∶ one → exp A two ∧
 ((bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
          sg A) ∘ f1) ∘ r∶ one → exp A two’
 by metis_tac[compose_hom] >>
irule ev_eq_eq >>
qexistsl_tac [‘A’,‘two’,‘one’] >> simp[] >>
‘p1 A one∶ (A × one) → A ∧ p2 A one∶ (A × one) → one’
 by metis_tac[p1_hom,p2_hom] >>
‘(((bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
          f1) ∘ r) ∘ p2 A one∶ (A × one) → exp A two’
 by metis_tac[compose_hom] >>
‘(((bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
          f0) ∘ r) ∘ p2 A one∶ (A × one) → exp A two’
 by metis_tac[compose_hom] >>
‘⟨p1 A one,(((bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
          f0) ∘ r) ∘ p2 A one⟩∶ (A × one) → (A × exp A two)’
  by metis_tac[pa_hom] >>
‘⟨p1 A one,(((bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
          f1) ∘ r) ∘ p2 A one⟩∶ (A × one) → (A × exp A two)’
  by metis_tac[pa_hom] >>
‘ev A two ∘
        ⟨p1 A one,(((bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
          f0) ∘ r) ∘ p2 A one⟩∶ (A × one) → two ∧
 ev A two ∘
        ⟨p1 A one,(((bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
          f1) ∘ r) ∘ p2 A one⟩∶ (A × one) → two’
 by metis_tac[compose_hom] >> irule fun_ext >>
qexistsl_tac [‘A × one’,‘two’] >> simp[] >>
rw[] >>
‘∃a0. a0∶ one → A ∧ a = ⟨a0, id one⟩’
 by metis_tac[to_p_with_1]>>
simp[] >>
‘(((bar f1 ∘
            tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
           f0) ∘ r) ∘ p2 A one =
 bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        (f0 ∘ r) ∘ p2 A one’
 by (irule compose_assoc_6_left_left_left_right2 >>
    metis_tac[]) >>
‘(((bar f1 ∘
            tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
           f1) ∘ r) ∘ p2 A one =
 bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        (f1 ∘ r) ∘ p2 A one’
 by (irule compose_assoc_6_left_left_left_right2 >>
    metis_tac[]) >>
‘(ev A two ∘
         ⟨p1 A one,(((bar f1 ∘
            tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
           f0) ∘ r) ∘ p2 A one⟩) ∘ ⟨a0,id one⟩ =
ev A two ∘
         ⟨p1 A one,bar f1 ∘
            tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
           (f0 ∘ r) ∘ p2 A one⟩ ∘ ⟨a0,id one⟩’
 by (simp[] >> irule compose_assoc >> metis_tac[]) >>
‘(ev A two ∘
         ⟨p1 A one,(((bar f1 ∘
            tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
           f1) ∘ r) ∘ p2 A one⟩) ∘ ⟨a0,id one⟩ =
ev A two ∘
         ⟨p1 A one,bar f1 ∘
            tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
           (f1 ∘ r) ∘ p2 A one⟩ ∘ ⟨a0,id one⟩’
 by (simp[] >>  irule compose_assoc >> metis_tac[]) >>
simp[] >>
‘f0 o r∶ one → A’ by metis_tac[compose_hom] >>
drule Thm6_g_ev' >> strip_tac >>
first_x_assum (qspecl_then [‘a0’,‘f0’,‘f1’,‘R’] assume_tac) >>
first_x_assum drule_all >> rw[] >>
‘f1 o r∶ one → A’ by metis_tac[compose_hom] >>
drule Thm6_g_ev' >> strip_tac >>
first_x_assum (qspecl_then [‘a0’,‘f0’,‘f1’,‘R’] assume_tac) >>
first_x_assum drule_all >> rw[] >>
‘ev A two ∘
              ⟨p1 A one,bar f1 ∘
              tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
              sg A ∘ (f0 ∘ r) ∘ p2 A one⟩ ∘ ⟨a0,id one⟩∶ one → two’
 by metis_tac[compose_hom] >>
‘ev A two ∘
         ⟨p1 A one,bar f1 ∘
         tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
         (f1 ∘ r) ∘ p2 A one⟩ ∘ ⟨a0,id one⟩∶ one → two’
 by metis_tac[compose_hom]  >>
irule one_to_two_eq >> simp[] >> rw[] >>
drule symm_trans_rel_lemma >> strip_tac >>
first_x_assum (qspecl_then [‘a0’,‘R’,‘A’,‘r’] assume_tac) >>
metis_tac[]
QED

Theorem Thm6_page29_means_just_that:
∀f0 f1 R A a0 a1.
         f0∶R → A ∧ f1∶R → A  ∧
         a0∶ one → A ∧ a1∶ one → A ∧
bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a0 =
bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a1 ⇒
∀a'. a'∶ one → A ⇒
    ((∃r. r∶one → R ∧ f0 ∘ r = a0 ∧ f1 ∘ r = a') ⇔
     (∃r. r∶one → R ∧ f0 ∘ r = a1 ∧ f1 ∘ r = a'))
Proof
rw[] >>
‘ev A two ∘
 ⟨p1 A one,bar f1 ∘
  tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘  a0 ∘ p2 A one⟩ ∘ ⟨a',id one⟩ = i2 one one ⇔
  ∃r. r∶one → R ∧ f0 ∘ r = a0 ∧ f1 ∘ r = a'’
  by (irule Thm6_g_ev' >> rw[]) >>
‘ev A two ∘
 ⟨p1 A one,bar f1 ∘
  tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘  a1 ∘ p2 A one⟩ ∘ ⟨a',id one⟩ = i2 one one ⇔
  ∃r. r∶one → R ∧ f0 ∘ r = a1 ∧ f1 ∘ r = a'’
  by (irule Thm6_g_ev' >> rw[]) >>
‘ev A two ∘
 ⟨p1 A one,bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a0 ∘ p2 A one⟩ ∘ ⟨a',id one⟩ =
 ev A two ∘
 ⟨p1 A one,bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a1 ∘ p2 A one⟩ ∘ ⟨a',id one⟩’
  suffices_by metis_tac[] >>
Q.UNDISCH_THEN
‘ev A two ∘
 ⟨p1 A one,bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a0 ∘ p2 A one⟩ ∘ ⟨a',id one⟩ =
        i2 one one ⇔ ∃r. r∶one → R ∧ f0 ∘ r = a0 ∧ f1 ∘ r = a'’
 (K ALL_TAC) >>
Q.UNDISCH_THEN
‘ev A two ∘
        ⟨p1 A one,bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a1 ∘ p2 A one⟩ ∘ ⟨a',id one⟩ =
        i2 one one ⇔ ∃r. r∶one → R ∧ f0 ∘ r = a1 ∧ f1 ∘ r = a'’
 (K ALL_TAC) >>
qabbrev_tac ‘l1 = bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a0’ >>
qabbrev_tac ‘l2 = bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a1’ >> 
‘bar f1∶ exp R two → exp A two’ by metis_tac[bar_thm] >>
‘ev A two∶ (A × exp A two) → two’ by metis_tac[ev_hom] >>
‘p1 R (exp A two)∶ (R × exp A two) → R ∧
 p2 R (exp A two)∶ (R × exp A two) → exp A two’
 by metis_tac[p1_hom,p2_hom] >>
‘f0 ∘ p1 R (exp A two)∶ (R × exp A two) → A’
 by metis_tac[compose_hom] >>
‘⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩∶
 (R × exp A two) → (A × (exp A two))’ by metis_tac[pa_hom] >>
‘ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩∶
 (R × exp A two) → two’ by metis_tac[compose_hom] >>
‘tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩)∶
 exp A two → exp R two’ by metis_tac[tp_hom] >>
‘⟨a',id one⟩∶ one → (A × one)’ by metis_tac[id1,pa_hom] >>
‘p1 A one∶ (A × one) → A ∧ p2 A one ∶ (A × one) → one’
 by metis_tac[p1_hom,p2_hom] >>
‘sg A∶ A → exp A two’ by metis_tac[sg_def] >>
‘bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a1 ∘ p2 A one∶ (A × one) → exp A two’
 by metis_tac[compose_hom] >>
‘bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a0 ∘ p2 A one∶ (A × one) → exp A two’
 by metis_tac[compose_hom] >>
‘⟨p1 A one,bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a0 ∘ p2 A one⟩∶ (A × one) → (A × exp A two)’
  by metis_tac[pa_hom] >>
‘⟨p1 A one,bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a1 ∘ p2 A one⟩∶ (A × one) → (A × exp A two)’
  by metis_tac[pa_hom] >>
‘l1∶ one → exp A two ∧ l2∶ one → exp A two’
 by (simp[Abbr‘l1’,Abbr‘l2’] >> metis_tac[compose_hom]) >> 
‘ev A two o ⟨p1 A one, l1 o p2 A one⟩ =
 ev A two o ⟨p1 A one, l2 o p2 A one⟩’
 by metis_tac[] >>
‘ev A two ∘
        ⟨p1 A one,bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a0 ∘ p2 A one⟩ =
 ev A two ∘
        ⟨p1 A one,bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a1 ∘ p2 A one⟩’
 suffices_by
  (rw[] >>
  ‘(ev A two ∘
        ⟨p1 A one,bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a0 ∘ p2 A one⟩) ∘ ⟨a',id one⟩ =
  ev A two ∘
        ⟨p1 A one,bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a0 ∘ p2 A one⟩ ∘ ⟨a',id one⟩ ∧
  (ev A two ∘
        ⟨p1 A one,bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a1 ∘ p2 A one⟩) ∘ ⟨a',id one⟩ =
  ev A two ∘
        ⟨p1 A one,bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a1 ∘ p2 A one⟩ ∘ ⟨a',id one⟩’
   suffices_by metis_tac[] >>
  strip_tac (* 2 *)
  >> irule compose_assoc >> metis_tac[compose_hom]) >>
qpat_x_assum ‘_ = _’ mp_tac >> fs[Abbr‘l1’,Abbr‘l2’] >>
‘(bar f1 ∘
         tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
         a0) ∘ p2 A one =
 bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a0 ∘ p2 A one ∧
 (bar f1 ∘
         tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
         a1) ∘ p2 A one =
 bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a1 ∘ p2 A one’  suffices_by metis_tac[] >>
strip_tac (* 2 *) >>
irule compose_assoc_5_4_left_SYM >> metis_tac[p2_hom]
(* assoc again... *)
QED

(*confused when should I use metis and irule...*)
     

Theorem compose_with_g_eq_equiv:
∀f0 f1 R A a0 a1.
         f0∶R → A ∧ f1∶R → A ∧ is_refl f0 f1 ∧
         a0∶ one → A ∧ a1∶ one → A ∧
bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a0 =
bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a1 ⇒
 ∃r. r∶ one → R ∧ f0 o r = a0 ∧ f1 o r = a1
Proof
rw[] >>
‘∀a'. a'∶one → A ⇒
       ((∃r. r∶one → R ∧ f0 ∘ r = a0 ∧ f1 ∘ r = a') ⇔
       ∃r. r∶one → R ∧ f0 ∘ r = a1 ∧ f1 ∘ r = a')’
 by (ho_match_mp_tac Thm6_page29_means_just_that >> rw[]) >>
    (* why metis_tac[Thm6_page29_means_just_that] does not work in this case *)
irule equiv_to_same_element >>   
metis_tac[equiv_to_same_element]
QED
    

                  
 


Theorem Thm6_page29_picture:
∀f0 f1 a0 a1 R A.
 f0∶ R → A ∧ f1∶ R → A ∧ is_symm f0 f1 ∧ is_trans f0 f1 ∧
 a0∶ one → A ∧ a1∶ one → A ⇒
 coeqa f0 f1 ∘ a0 = coeqa f0 f1 ∘ a1 ⇒
 bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a0 =
 bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a1
Proof  
rw[] >>
‘(bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
          sg A) ∘ f0 =
         (bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
          sg A) ∘ f1’ by metis_tac[f0g_eq_f1g] >>
‘bar f1∶ exp R two → exp A two’ by metis_tac[bar_thm] >>
‘sg A∶ A → exp A two’ by metis_tac[sg_def] >>
‘ev A two∶ (A × exp A two) → two’ by metis_tac[ev_hom] >>
‘p1 R (exp A two)∶ (R × exp A two) → R ∧
 p2 R (exp A two)∶ (R × exp A two) → exp A two’
 by metis_tac[p1_hom,p2_hom] >>
‘f0 ∘ p1 R (exp A two)∶ (R × exp A two) → A’
 by metis_tac[compose_hom] >>
‘⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩∶
 (R × exp A two) → (A × (exp A two))’ by metis_tac[pa_hom] >>
‘ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩∶
 (R × exp A two) → two’ by metis_tac[compose_hom] >>
‘tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩)∶
 exp A two → exp R two’ by metis_tac[tp_hom] >>
‘(bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A)∶ A → exp A two’
 by metis_tac[compose_hom] >>
qabbrev_tac ‘l = (bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A)’ >>
‘(bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
        sg A) ∘ a0 =
 (bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
        sg A) ∘ a1’
 suffices_by
  (strip_tac >>
  ‘(bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘ a0 =
   bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
   sg A ∘ a0 ∧
   (bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘ a1 =
   bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
   sg A ∘ a1’ suffices_by metis_tac[] >>
  strip_tac (* 2 *) >> irule compose_assoc_4_3_left >> metis_tac[])>>
simp[] >>
‘∃u. u∶ coeqo f0 f1 → exp A two ∧ u o coeqa f0 f1 = l’
 suffices_by
  (rw[] >>
  ‘coeqa f0 f1∶ A → coeqo f0 f1’ by metis_tac[coeqa_hom] >>
  metis_tac[compose_assoc]) >>
qexists_tac ‘coeq_induce f0 f1 l’ >> rw[] (* 2 *)
>- metis_tac[coeq_induce_hom]
>- metis_tac[coeq_fac]
QED


        

Theorem Thm6:
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ∧
            is_refl f0 f1 ∧ is_symm f0 f1 ∧ is_trans f0 f1 ∧
            is_mono ⟨f0, f1⟩ ⇒
            R ≅ eqo ((coeqa f0 f1) o p1 A A)
                    ((coeqa f0 f1) o p2 A A)
Proof
rw[] >> irule Thm6_first_sentence >> rw[] >>
irule equiv_to_same_element >> rw[] >> qexists_tac ‘A’ >>
simp[] >> 
ho_match_mp_tac Thm6_page29_means_just_that >> rw[] >>
irule Thm6_page29_picture >> rw[]
QED                    

val _ = export_theory();
