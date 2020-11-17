open HolKernel Parse boolLib bossLib;

open ETCSaxiomTheory basicTheory;     

open Thm3Theory;
     
val _ = new_theory "Thm6";


Theorem pb_exists_thm = SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] pb_exists        


val pb_def = new_specification ("pb_def",["pbo","pb1","pb2"],pb_exists_thm)

Theorem iso_symm:
∀X Y. X ≅ Y ⇔ Y ≅ X
Proof
cheat
QED    

Theorem iso_trans:
∀X Y Z. X ≅ Y ∧ Y ≅ Z ⇒ X ≅ Z
Proof
cheat
QED

Theorem iso_to_same:
∀X Y A. X ≅ A ∧ Y ≅ A ⇒ X ≅ Y
Proof
metis_tac[iso_symm,iso_trans]
QED        


    
Theorem inc_inc_iso0:
∀A X Y a b h1 h2. is_mono a ∧ is_mono b ∧ a∶ X → A ∧ b∶ Y → A ∧
                  h1∶ X → Y ∧ h2∶ Y → X ∧
                  b o h1 = a ∧ a o h2 = b ⇒ X ≅ Y
Proof
rw[] >> Cases_on ‘X ≅ zero’ >> Cases_on ‘Y ≅ zero’
>- metis_tac[iso_to_same]
>- metis_tac[to_zero_zero]
>- metis_tac[to_zero_zero]
>- (qabbrev_tac ‘b = a o h2’ >>
   ‘∃b'. b'∶ A → Y ∧ b' o b = id Y’
    by metis_tac[mono_non_zero_post_inv] >>
   ‘∃a'. a'∶ A → X ∧ a' o a = id X’
    by metis_tac[mono_non_zero_post_inv] >>
   simp[are_iso_is_iso] >>
   qexists_tac ‘h1’ >>
   ‘h1 o h2 = id Y ∧ h2 o h1 = id X’
    suffices_by metis_tac[is_iso_thm] >>
   strip_tac (* 2 *)
   >- (‘b' o (a o h2) = id Y’
       by metis_tac[Abbr‘b’] >>
      ‘b' o b o h1 = b' o a’
       by metis_tac[] >>
      ‘h1 = b' o a’ by metis_tac[idL, compose_assoc] >>
      metis_tac[compose_assoc])
   >- (‘a' o a o h2 = a' o b’
       by metis_tac[Abbr‘b’] >>
      ‘h2 = a' o b’ by metis_tac[idL,compose_assoc] >>
      metis_tac[compose_assoc]))
QED


Theorem prop_2_half2:
∀X Y A a b. is_mono a ∧ is_mono b ∧ a∶ X → A ∧ b∶ Y → A ∧
            (∀x xb. x∶ one → A ∧ xb∶ one → X ∧ a o xb = x ⇒
                    ∃xb'. xb'∶ one → Y ∧ b o xb' = x) ⇒
            (∃h. h∶ X → Y ∧ b o h = a)
Proof
rpt strip_tac >> Cases_on ‘Y≅ zero’
>- cheat
>- (‘∃g. g∶ A → Y ∧ g o b = id Y’
    by metis_tac[mono_non_zero_post_inv] >>
   qexists_tac ‘g o a’ >> strip_tac
   >- metis_tac[compose_hom] >> 
   irule fun_ext >>
   ‘b ∘ g ∘ a∶ X → A ∧ a∶ X → A’ by metis_tac[compose_hom] >>
   qexistsl_tac [‘X’,‘A’] >> simp[] >> rpt strip_tac >>
   rename [‘x0∶ one → X’] >>
   first_x_assum (qspecl_then [‘a o x0’,‘x0’] assume_tac) >>
   ‘a o x0∶ one → A’ by metis_tac[compose_hom] >>
   fs[] >> rfs[] >>
   ‘(b ∘ g ∘ a) ∘ x0 = b ∘ g ∘ (a ∘ x0)’
    by metis_tac[compose_assoc_4_3_left] >>
   ‘b ∘ g ∘ a ∘ x0 = b o g o b o xb'’
    by metis_tac[] >>
   ‘b ∘ g ∘ b ∘ xb' = b ∘ (g ∘ b) ∘ xb'’
    by metis_tac[compose_assoc_4_2_left_middle,
                 compose_assoc_4_2_left] >>
   ‘b ∘ (g ∘ b) ∘ xb' = b o xb'’
     by metis_tac[idL] >>
   metis_tac[])
QED


Theorem prop_2_corollary:
∀X Y A a b. a∶ X → A ∧ b∶ Y → A ∧ is_mono a ∧ is_mono b ∧
            (∀y. y∶ one → Y ⇒ ∃x. x∶ one → X ∧ a o x = b o y) ∧
            (∀x. x∶ one → X ⇒ ∃y. y∶ one → Y ∧ a o x = b o y) ⇒
            X ≅ Y
Proof
rw[] >> irule inc_inc_iso0 >>
‘∃h1. h1∶ X → Y ∧ b o h1 = a’
 by (irule prop_2_half2 >> rw[] >> metis_tac[]) >>
‘∃h2. h2∶ Y → X ∧ a o h2 = b’
 by (irule prop_2_half2 >> rw[] >> metis_tac[]) >>
metis_tac[]
QED

        


Definition is_refl_def:
is_refl f0 f1 ⇔ dom f0 = dom f1 ∧ cod f0 = cod f1 ∧
             ∃d. d∶ cod f1 → dom f1 ∧
                 f0 o d = id (cod f1) ∧
                 f1 o d = id (cod f1)
End


Definition is_symm_def:
is_symm f0 f1 ⇔ dom f0 = dom f1 ∧ cod f0 = cod f1 ∧
             ∃t. t∶ dom f1 → dom f1 ∧
                 f0 o t = f1 ∧
                 f1 o t = f0
End


Definition is_trans_def:
is_trans f0 f1 ⇔ dom f0 = dom f1 ∧ cod f0 = cod f1 ∧
                 ∀X h0 h1.
                  h0∶ X → dom f1 ∧ h1∶ X → dom f1 ∧
                  f1 o h0 = f0 o h1 ⇒
                  ∃u. u∶ X → dom f1 ∧
                      f0 o u = f0 o h0 ∧ f1 o u = f1 o h1
End

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


Theorem char_exists:
∀a. is_mono a ⇒ ∃phi. phi∶ cod a → (one + one) ∧
    ∀x. x∶ one → cod a ⇒ ((∃x0. x0∶ one → dom a ∧ a o x0 = x) ⇔
                         phi o x = i2 one one)
Proof
cheat
QED
     

Theorem char_exists_thm = SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] char_exists        

val char_def = new_specification ("char_def",["char"],char_exists_thm)
(*
Theorem sing_exists:
∀A. ∃s. s∶ A → exp A 2 ∧
    ∀x y. x∶ one → A ∧ y∶ one → A ⇒
    (∃y0. y0∶ one → eqo () ((i2 one one) o (to1 A))) ⇔
    y = x
        *)


Theorem char_thm:
∀a A X.
    is_mono a ∧ a∶ A → X ⇒
         char a∶ X → one + one ∧
         ∀x.
             x∶one → X ⇒
             ((∃x0. x0∶one → A ∧ a ∘ x0 = x) ⇔ char a ∘ x = i2 one one)
Proof
cheat
QED


Definition n2a_def:
n2a f = 

(*n2a sends a 1 --> 2^A  to transpose, a2n other direction*)

  ev A (one + one) o ⟨p1 A one, hb o tp (psi o p2 one R)⟩



Theorem fac_char:
∀m A X. is_mono m ∧ m∶ A → X ⇒
        ∀P p f. p∶ P → X ∧ f∶ P → A ∧ m o f = p ⇒
                char m o p = (i2 one one) ∘ to1 P
Proof
cheat
QED

Theorem iso_zero_zero:
∀A. A≅ zero ⇒
   ∀X. ∃!f. f∶ A → X
Proof
rw[EXISTS_UNIQUE_ALT] >>
‘∃i. i∶A → zero ∧ is_iso i’ by metis_tac[are_iso_is_iso] >>
qexists_tac ‘(from0 X) o i’ >>
rw[EQ_IMP_THM] >> metis_tac[from_iso_zero_eq,ax1_2,compose_hom]
QED

Theorem epi_has_section:
∀e A B. is_epi e ∧ e∶ A → B ⇒ ∃s. s∶ B → A ∧ e o s = id B
Proof
rw[] >> Cases_on ‘B ≅ zero’
>- (drule iso_zero_zero >> rw[] >>
   fs[EXISTS_UNIQUE_ALT] >>
   ‘∃f. ∀f'. f'∶B → A ⇔ f = f'’ by metis_tac[] >>
   qexists_tac ‘f’ >>
   metis_tac[id1,compose_hom])
>- metis_tac[epi_pre_inv]
QED

        

Theorem fac_char_via_any_map:
∀f A B M m e b. is_epi e ∧ is_mono m ∧ f = m o e ∧
              f∶ A → B ∧ e∶ A → M ∧ m∶ M → B ∧
              b∶ one → B ∧ (char m) o b = i2 one one ⇒
              ∃a. a∶ one → A ∧ f o a = b
Proof
rw[] >> drule epi_has_section >> rw[] >>
first_x_assum drule >> rw[] >>
drule char_thm >> rw[] >> first_x_assum drule >> rw[] >>
first_x_assum (qspec_then ‘b’ assume_tac) >> rfs[] >>
qexists_tac ‘s' o x0’ >>
‘s' o x0 ∶ one → A’ by metis_tac[compose_hom] >> simp[] >>
‘(m ∘ e) ∘ s' ∘ x0 = m ∘ (e ∘ s') ∘ x0’
 by metis_tac[compose_assoc_4_2_left_middle] >>
metis_tac[idL,idR]
QED

              
               
        
Theorem Thm6_lemma_3:
∀h R A. h∶ R → A ⇒
        ∃hb. hb∶ exp R (one + one) → exp A (one + one) ∧
             (∀psi. psi∶ R → one + one ⇒
                    ∀x. x∶ one → A ⇒
                        (ev A (one + one) o ⟨p1 A one, hb o tp (psi o p1 R one)⟩ o ⟨id A, to1 A⟩ o x = i2 one one ⇔
                         ∃r. r∶ one → R ∧
                             psi o r = i2 one one ∧
                             h o r = x))
Proof
rw[] >>
qabbrev_tac ‘two = one + one’ >> 
‘ev R two∶ (R × (exp R two)) → two’ by metis_tac[ev_hom] >>
qabbrev_tac ‘i₀ = i1 one one’ >>
qabbrev_tac ‘i₁ = i2 one one’ >>
‘i₀∶  one → two ∧ i₁∶ one → two’
 by (simp[Abbr‘i₀’,Abbr‘i₁’,Abbr‘two’] >>
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
‘ϕ∶A × exp R two → two’ by simp[Abbr‘two’] >>
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
                        ψ o r' = ⟨r, tp (psi ∘ p1 R one)⟩)’ by cheat >>
simp[EQ_IMP_THM] >> rpt strip_tac (* 2 *)
>- ‘ϕ o ⟨x, tp (psi ∘ p1 R one)⟩ =
    ev A two ∘ ⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 R one)⟩ ∘ ⟨id A,to1 A⟩ ∘ x’ by cheat >>
   (*need lemma*)
   (*use fact that epi has section*)
   ‘ϕ o ⟨x, tp (psi ∘ p1 R one)⟩ = i₁’ by metis_tac[] >>
   drule fac_char_via_any_map >> strip_tac >>
   first_x_assum (qspecl_then [‘h2R o ψ’,‘R'’,‘A × (exp R two)’,
                               ‘M’,‘m’,
                               ‘⟨x,tp (psi o p1 R one)⟩’]
                  assume_tac) >>
   ‘∃r'. r'∶one → R' ∧ (h2R ∘ ψ) ∘ r' = ⟨x,tp (psi ∘ p1 R one)⟩’
     by cheat >>
  (* ‘(p1 A (exp R two))∶ (A × (exp R two)) → A ∧
    (p2 A (exp R two))∶ (A × (exp R two)) → (exp R two)’
    by metis_tac[p1_hom,p2_hom] >> (*move to the top...*)*)
   ‘(p1 R (exp R two)) o ψ o r'∶ one → R’
    by metis_tac[compose_hom] >>
   qexists_tac ‘(p1 R (exp R two)) o ψ o r'’ >>
   simp[] >>
   rw[] (* 2 *)
   >- qexists_tac ‘r'’ >> simp[] >>
      ‘psi o (p1 R one)∶ (R × one) → two’
       by metis_tac[compose_hom,p1_hom] >>
      ‘tp (psi ∘ p1 R one)∶ one → exp R two’
        by metis_tac[tp_hom] >>
      ‘p2 R (exp R two) o ψ ∘ r' =
       tp (psi ∘ p1 R one)’ suffices_by cheat >>
      ‘p2 A (exp R two) o (h2R ∘ ψ) ∘ r' =
       p2 A (exp R two) o ⟨x,tp (psi ∘ p1 R one)⟩’
       by metis_tac[] >>
      ‘p2 A (exp R two) o ⟨x,tp (psi ∘ p1 R one)⟩ =
       tp (psi ∘ p1 R one)’ by metis_tac[p2_of_pa] >>
      ‘p2 R (exp R two) = p2 A (exp R two) o h2R’
        by cheat >>
      simp[] >>
      cheat
   >-    
   
   1
        
>- ‘ev A two ∘ ⟨p1 A one,tp ϕ ∘ tp (psi ∘ p2 one R)⟩ ∘ ⟨id A,to1 A⟩ ∘ x = ϕ o ⟨x, tp (psi ∘ p2 one R)⟩’ by cheat >>
   simp[SimpLHS] >>
   ‘∃r'. r'∶one → R' ∧ ψ ∘ r' = ⟨r, tp (psi ∘ p2 one R)⟩’
    by metis_tac[] >>
   Q.UNDISCH_THEN
   ‘∀r.  r∶one → R ⇒
            (psi ∘ r = i₁ ⇔
             ∃r'. r'∶one → R' ∧ ψ ∘ r' = ⟨r,tp (psi ∘ p2 one R)⟩)’ (K ALL_TAC) >>
   ‘(h2R o ψ) ∘ r' = h2R o ⟨r, tp (psi ∘ p2 one R)⟩’
    by metis_tac[compose_assoc] >>
   ‘m o e o r' = h2R ∘ ⟨r, tp (psi ∘ p2 one R)⟩’
    by metis_tac[compose_assoc] >>
   ‘ϕ ∘ h2R ∘ ⟨r,tp (psi ∘ p2 one R)⟩ = i₁’ by cheat >>
   ‘h2R ∘ ⟨r,tp (psi ∘ p2 one R)⟩ = ⟨x,tp (psi ∘ p2 one R)⟩’
    by cheat >>
   metis_tac[]
   (*use fac_char*)
  
                  

            
                                
Theorem Thm6_symm_unique_g:
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ∧
            is_symm f0 f1 ⇒
Proof
cheat
QED                        

Theorem Thm6:
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ∧
            is_refl f0 f1 ∧ is_symm f0 f1 ∧ is_trans f0 f1 ∧
            is_mono ⟨f0, f1⟩ ⇒
            R ≅ eqo ((coeqa f0 f1) o p1 A A)
                    ((coeqa f0 f1) o p2 A A)
Proof
rw[] >> irule Thm6_first_sentence >> rw[]
QED                    

val _ = export_theory();
