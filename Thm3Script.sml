
Theorem fac_through_zero:
∀A B X f g h. f∶ A → B ∧ g∶ A → X ∧ h∶ X→ B ∧ f = h o g ∧ X ≅ zero ⇒ A ≅ zero
Proof
cheat
QED
        

Theorem Thm3_case_zero:
∀A B f h. f∶ A → B ∧ A≅ zero ∧
          h∶ (coeqo ((p1 A A) o (eqa (f o p1 A A) (f o p2 A A)))
                    ((p2 A A) o (eqa (f o p1 A A) (f o p2 A A)))) →
             (eqo ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
                  ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B))) ∧
          (eqa ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
               ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B))) o h o
          (coeqa (p1 A A o (eqa (f o p1 A A) (f o p2 A A)))
                 (p2 A A o (eqa (f o p1 A A) (f o p2 A A))))  = f ⇒
          is_iso h
Proof
cheat
QED          


Theorem Thm3_case_non_zero:
∀A B f h. f∶ A → B ∧ ¬(A≅ zero) ∧
          h∶ (coeqo ((p1 A A) o (eqa (f o p1 A A) (f o p2 A A)))
                    ((p2 A A) o (eqa (f o p1 A A) (f o p2 A A)))) →
             (eqo ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
                  ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B))) ∧
          (eqa ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
               ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B))) o h o
          (coeqa (p1 A A o (eqa (f o p1 A A) (f o p2 A A)))
                 (p2 A A o (eqa (f o p1 A A) (f o p2 A A))))  = f ⇒
          is_iso h
Proof
rw[] >>
qabbrev_tac ‘I' = (coeqo ((p1 A A) o (eqa (f o p1 A A) (f o p2 A A)))
                  ((p2 A A) o (eqa (f o p1 A A) (f o p2 A A))))’ >>
qabbrev_tac ‘I0 = (eqo ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
                  ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B)))’ >>
qabbrev_tac ‘k = eqa (f o p1 A A) (f o p2 A A)’ >>
qabbrev_tac ‘k' = coeqa (i1 B B o f) (i2 B B o f)’ >>
qabbrev_tac ‘q = coeqa (p1 A A o k) (p2 A A o k)’ >>
qabbrev_tac ‘q' = eqa (k' o i1 B B) (k' o i2 B B)’ >>
qabbrev_tac ‘R = eqo (f o (p1 A A)) (f o (p2 A A))’ >>
qabbrev_tac ‘R' = coeqo ((i1 B B) o f) ((i2 B B) o f)’ >>
‘p1 A A∶ A×A → A ∧ p2 A A∶ A×A → A’ by metis_tac[p1_hom,p2_hom] >>
‘i1 B B∶ B → B + B ∧ i2 B B∶ B → B + B’ by metis_tac[i1_hom,i2_hom] >>
‘f o p1 A A∶ A× A → B ∧ f o p2 A A∶ A × A → B ∧
 i1 B B o f∶ A → B + B ∧ i2 B B o f∶ A → B + B’ by metis_tac[compose_hom] >>
‘k∶ R → (A× A)’ by (simp[Abbr‘k’,Abbr‘R’] >> metis_tac[eqa_hom]) >>
‘p1 A A o k∶ R → A ∧ (p2 A A ∘ k)∶ R → A’ by metis_tac[compose_hom] >>
‘q∶ A → I'’ by (simp[Abbr‘I'’,Abbr‘q’] >> metis_tac[coeqa_hom]) >>
‘k'∶ (B + B) → R'’ by (simp[Abbr‘k'’,Abbr‘R'’] >> metis_tac[coeqa_hom]) >>
‘k' o i1 B B∶ B → R' ∧ k' o i2 B B∶ B → R'’ by metis_tac[compose_hom] >> 
‘q'∶ I0 → B’ by (simp[Abbr‘q'’,Abbr‘I0’] >> metis_tac[eqa_hom]) >>
‘is_mono k’ by (simp[Abbr‘k’] >> metis_tac[eqa_is_mono]) >>
‘is_mono q'’ by (simp[Abbr‘q'’] >> metis_tac[eqa_is_mono]) >>
‘is_epi q ∧ is_epi k'’ by (simp[Abbr‘q’,Abbr‘k’] >> metis_tac[coeqa_is_epi]) >>
irule mono_epi_is_iso >> strip_tac (* 2 *)
>- (‘is_epi (h o q)’ suffices_by metis_tac[o_epi_imp_epi] >>
   irule is_epi_applied >>
   ‘h o q∶ A → I0’ by metis_tac[compose_hom] >>
   qexistsl_tac [‘A’,‘I0’] >> rw[] >>
   rename [‘u ∘ h ∘ q = u' ∘ h ∘ q’] >>
   ‘¬(I0 ≅ zero)’
    by
     (SPOSE_NOT_THEN ASSUME_TAC >> ‘A≅ zero’ suffices_by metis_tac[] >>
      irule fac_through_zero >>
      qexistsl_tac [‘B’,‘I0’,‘q' o h o q’,‘h o q’,‘q'’] >> metis_tac[]) >>
  qabbrev_tac ‘f = q' o h o q’ >>
  ‘∃qi.qi∶ B → I0 ∧ qi o q' = id I0’ by metis_tac[mono_non_zero_post_inv] >>
  ‘u o qi∶ B → X ∧ u' o qi∶ B → X’ by metis_tac[compose_hom] >>
  ‘copa (u o qi) (u' o qi)∶ (B + B) → X’ by metis_tac[copa_hom] >> 
  ‘copa (u o qi) (u' o qi) o (i1 B B) o f =
   copa (u o qi) (u' o qi) o (i2 B B) o f’
    by
     (irule o_bracket_right >> reverse (strip_tac) (* 2 *)
      >- (qexistsl_tac [‘X’,‘A’,‘B’,‘B + B’] >> rw[])
      >- (‘(copa (u ∘ qi) (u' ∘ qi) ∘ i1 B B) = u o qi’
           by metis_tac[i1_of_copa] >>
         ‘(copa (u ∘ qi) (u' ∘ qi) ∘ i2 B B) = u' o qi’
           by metis_tac[i2_of_copa] >>
         rw[] >> simp[Abbr‘f’] >>
         ‘(u ∘ qi) ∘ q' ∘ h ∘ q = u ∘ (qi ∘ q') ∘ h ∘ q ∧
          (u' ∘ qi) ∘ q' ∘ h ∘ q = u' ∘ (qi ∘ q') ∘ h ∘ q ’
           by metis_tac[compose_assoc] >>
         metis_tac[idL,idR,compose_assoc])) >>
  ‘coeq_induce (i1 B B o f) (i2 B B o f) (copa (u ∘ qi) (u' ∘ qi))∶ R' → X’
    by (simp[Abbr‘R'’] >> metis_tac[coeq_induce_hom]) >>
  qabbrev_tac
   ‘w = coeq_induce (i1 B B ∘ f) (i2 B B ∘ f) (copa (u ∘ qi) (u' ∘ qi))’ >>
  ‘w o k' = (copa (u ∘ qi) (u' ∘ qi))’
    by (simp[Abbr‘w’,Abbr‘k'’] >> metis_tac[coeq_fac]) >>
  ‘(u o qi) o q' = (u' o qi) o q'’ suffices_by metis_tac[idR,compose_assoc] >>
  ‘u o qi = (copa (u ∘ qi) (u' ∘ qi)) o i1 B B ∧
   u' o qi = (copa (u ∘ qi) (u' ∘ qi)) o i2 B B’
   by metis_tac[i1_of_copa,i2_of_copa] >>
  ‘copa (u ∘ qi) (u' ∘ qi) ∘ i1 B B o q' =
   copa (u ∘ qi) (u' ∘ qi) ∘ i2 B B o q'’suffices_by metis_tac[compose_assoc]>>
  ‘w o k' ∘ i1 B B ∘ q' =
   w o k' ∘ i2 B B ∘ q'’ suffices_by metis_tac[compose_assoc] >>
  ‘k' ∘ i1 B B ∘ q' = k' ∘ i2 B B ∘ q'’ suffices_by metis_tac[] >>
  simp[Abbr‘q'’] >>
  ‘(k' ∘ i1 B B) ∘ eqa (k' ∘ i1 B B) (k' ∘ i2 B B) =
   (k' ∘ i2 B B) ∘ eqa (k' ∘ i1 B B) (k' ∘ i2 B B)’
    suffices_by metis_tac[compose_assoc] >>
  metis_tac[eq_equlity])
>- (‘is_mono (q' o h)’ suffices_by metis_tac[o_mono_imp_mono](*o_mono_mono*) >>
   ‘∃t. t∶ I' → A ∧ q o t = id I'’ by metis_tac[epi_non_zero_pre_inv] >> 
   ‘f o t = q' o h’
     by
      (‘(q' ∘ h ∘ q) o t = f o t’ by metis_tac[] >>
       ‘h o q∶ A → I0’ by metis_tac[compose_hom] >>
       ‘(q' ∘ h ∘ q) o t = q' ∘ h ∘ q o t ’ by metis_tac[compose_assoc] >>
       metis_tac[compose_hom,idR,id1]) >>
   irule is_mono_applied >>
   ‘q' o h∶ I' → B’ by metis_tac[compose_hom] >>
   qexistsl_tac [‘I'’,‘B’] >> simp[] >> rpt strip_tac >>
   rename [‘(q' ∘ h) ∘ u = (q' ∘ h) ∘ u'’] >>
   ‘t o u∶ X → A ∧ t o u'∶ X→ A’ by metis_tac[compose_hom] >>
   ‘f o (p1 A A) o ⟨t o u, t o u'⟩ =
    f o (p2 A A) o ⟨t o u, t o u'⟩’
      by
       (‘f o (p1 A A) o ⟨t o u, t o u'⟩ =
         f o t o u’ by metis_tac[p1_of_pa] >>
        ‘f o t o u = q' o h o u’ by metis_tac[compose_hom,compose_assoc] >>
        ‘q' o h o u = q' o h o u'’ by metis_tac[compose_hom,compose_assoc] >>
        ‘q' o h o u' = f o t o u'’ by metis_tac[compose_hom,compose_assoc] >>
        ‘f o t o u' = f o (p2 A A) o ⟨t o u, t o u'⟩’ by metis_tac[p2_of_pa] >> 
        metis_tac[]) >>
   ‘⟨t o u,t o u'⟩∶ X → (A×A)’ by metis_tac[pa_hom] >> 
   ‘∃w. w∶ X → R ∧ k o w = ⟨t o u, t o u'⟩’
        by
         (qexists_tac
          ‘eq_induce (f ∘ p1 A A) (f ∘ p2 A A) ⟨t ∘ u,t ∘ u'⟩’ >>
          ‘(f ∘ p1 A A) ∘ ⟨t ∘ u,t ∘ u'⟩ = (f ∘ p2 A A) ∘ ⟨t ∘ u,t ∘ u'⟩’
            by metis_tac[o_bracket_left] >>
          ‘(f ∘ p1 A A)∶ (A× A) → B’ by metis_tac[compose_hom,p1_hom] >>
          ‘(f ∘ p2 A A)∶ (A× A) → B’ by metis_tac[compose_hom,p2_hom] >>
          strip_tac (*2 *)
          >- (simp[Abbr‘R’] >> metis_tac[ax1_5_applied])
          >- (simp[Abbr‘k’] >> metis_tac[eq_fac])
         ) >>
   ‘u = q o t o u’ by metis_tac[id1,idL,compose_assoc] >>
   ‘t o u = (p1 A A) o ⟨t o u, t o u'⟩’ by metis_tac[p1_of_pa] >> 
       (*need add hom to assumption later*)
   ‘q o t o u = q o (p1 A A) o ⟨t o u, t o u'⟩’ by metis_tac[] >>
   ‘q o (p1 A A) o ⟨t o u, t o u'⟩ = q o p1 A A o k o w’
         by metis_tac[compose_assoc,compose_hom] >>
   ‘q o (p1 A A) o k = q o (p2 A A) o k’
     by
      (simp[Abbr‘q’] >> metis_tac[coeq_equlity]) >>
   ‘q o p1 A A o k o w =  q o (p2 A A) o k o w’
     by metis_tac[compose_hom,compose_assoc] >> 
   ‘q o (p2 A A) o k o w = q o (p2 A A) o ⟨t o u, t o u'⟩’ by metis_tac[] >>
   ‘q o (p2 A A) o ⟨t o u, t o u'⟩ = q o t o u'’
     by metis_tac[compose_hom,compose_assoc,p2_of_pa] >>
   ‘q o t o u' = u'’ by metis_tac[id1,idL,compose_assoc]>>
   metis_tac[])
QED



Theorem unique_h_lemma:
∀A B C D f g q k h. f∶ A → B ∧ g∶D → B ∧ q∶ A → C ∧  
              (∀k'. (k'∶ A→ D ∧ g o k' = f) ⇔ k' = k) ∧
              (∀h'. (h'∶ C → D ∧ h' o q = k) ⇔ h' = h) ⇒
              ∃!h. h∶ C → D ∧ g o h o q = f
Proof
rw[EXISTS_UNIQUE_ALT] >> qexists_tac ‘h’ >> rw[EQ_IMP_THM] >>
metis_tac[compose_assoc,compose_hom]
QED

Theorem Thm3_f_fac_eq:
∀A B f hb. hb∶ A → eqo ((eqa (i1 B B o f) (i2 B B o f)) o i1 B B)
                       ((eqa (i1 B B o f) (i2 B B o f)) o i2 B B) ∧
            eqa ((coeqa (i1 B B ∘ f) (i2 B B ∘ f)) ∘ i1 B B)
                 (coeqa (i1 B B ∘ f) (i2 B B ∘ f) ∘ i2 B B) o hb = f ⇔
            hb = eq_induce (coeqa (i1 B B ∘ f) (i2 B B ∘ f) o i1 B B)
                           (coeqa (i1 B B ∘ f) (i2 B B ∘ f) o i2 B B)
                           f
Proof
cheat
QED


        

Theorem Thm3_h_exists:
∀A B f.
         f∶A → B ⇒
       ∃!h.  h∶coeqo (p1 A A ∘ eqa (f ∘ p1 A A) (f ∘ p2 A A))
           (p2 A A ∘ eqa (f ∘ p1 A A) (f ∘ p2 A A)) →
         eqo (coeqa (i1 B B ∘ f) (i2 B B ∘ f) ∘ i1 B B)
           (coeqa (i1 B B ∘ f) (i2 B B ∘ f) ∘ i2 B B) ∧
         eqa (coeqa (i1 B B ∘ f) (i2 B B ∘ f) ∘ i1 B B)
           (coeqa (i1 B B ∘ f) (i2 B B ∘ f) ∘ i2 B B) ∘ h ∘
         coeqa (p1 A A ∘ eqa (f ∘ p1 A A) (f ∘ p2 A A))
           (p2 A A ∘ eqa (f ∘ p1 A A) (f ∘ p2 A A)) =
         f
Proof
rw[] >>
qabbrev_tac ‘I' = (coeqo ((p1 A A) o (eqa (f o p1 A A) (f o p2 A A)))
                  ((p2 A A) o (eqa (f o p1 A A) (f o p2 A A))))’ >>
qabbrev_tac ‘I0 = (eqo ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
                  ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B)))’ >>
qabbrev_tac ‘k = eqa (f o p1 A A) (f o p2 A A)’ >>
qabbrev_tac ‘k' = coeqa (i1 B B o f) (i2 B B o f)’ >>
qabbrev_tac ‘q = coeqa (p1 A A o k) (p2 A A o k)’ >>
qabbrev_tac ‘q' = eqa (k' o i1 B B) (k' o i2 B B)’ >>
qabbrev_tac ‘R = eqo (f o (p1 A A)) (f o (p2 A A))’ >>
qabbrev_tac ‘R' = coeqo ((i1 B B) o f) ((i2 B B) o f)’ >>
‘p1 A A∶ A×A → A ∧ p2 A A∶ A×A → A’ by metis_tac[p1_hom,p2_hom] >>
‘i1 B B∶ B → B + B ∧ i2 B B∶ B → B + B’ by metis_tac[i1_hom,i2_hom] >>
‘f o p1 A A∶ A× A → B ∧ f o p2 A A∶ A × A → B ∧
 i1 B B o f∶ A → B + B ∧ i2 B B o f∶ A → B + B’ by metis_tac[compose_hom] >>
‘k∶ R → (A× A)’ by (simp[Abbr‘k’,Abbr‘R’] >> metis_tac[eqa_hom]) >>
‘p1 A A o k∶ R → A ∧ (p2 A A ∘ k)∶ R → A’ by metis_tac[compose_hom] >>
‘q∶ A → I'’ by (simp[Abbr‘I'’,Abbr‘q’] >> metis_tac[coeqa_hom]) >>
‘k'∶ (B + B) → R'’ by (simp[Abbr‘k'’,Abbr‘R'’] >> metis_tac[coeqa_hom]) >>
‘k' o i1 B B∶ B → R' ∧ k' o i2 B B∶ B → R'’ by metis_tac[compose_hom] >> 
‘q'∶ I0 → B’ by (simp[Abbr‘q'’,Abbr‘I0’] >> metis_tac[eqa_hom]) >>
irule unique_h_lemma >>
qabbrev_tac ‘c = eq_induce (k' ∘ i1 B B) (k' ∘ i2 B B) f’ >> 
qexistsl_tac [‘A’,‘B’,
              ‘coeq_induce (p1 A A ∘ k) (p2 A A ∘ k) c’,
              ‘c’] >>
              (*
‘(∀k'. k'∶A → I0 ∧ q' ∘ k' = f ⇔ k' = c)’*)
‘(k' o (i1 B B)) o  f = (k' o (i2 B B)) o f’
  by (simp[Abbr‘k'’] >>
     ‘coeqa (i1 B B ∘ f) (i2 B B ∘ f) ∘ i1 B B ∘ f =
      coeqa (i1 B B ∘ f) (i2 B B ∘ f) ∘ i2 B B ∘ f’
      suffices_by metis_tac[compose_assoc] >>
     metis_tac[coeq_equlity]) >>
drule eq_fac_unique >> strip_tac >>
first_x_assum (qspecl_then [‘B’,‘R'’,‘A’] assume_tac) >>
‘∀h0. (h0∶A → eqo (k' ∘ i1 B B) (k' ∘ i2 B B) ∧
       eqa (k' ∘ i1 B B) (k' ∘ i2 B B) ∘ h0 = f ⇔
       h0 = eq_induce (k' ∘ i1 B B) (k' ∘ i2 B B) f)’ by metis_tac[] >>
strip_tac (* 2 *)      
>- (simp[Abbr‘I0’] >> simp[Abbr‘q'’] >> simp[]) >>

‘is_mono q'’ by (simp[Abbr‘q'’] >> metis_tac[eqa_is_mono]) >>
(*‘c o p1 A A o k = c o p2 A A o k’*)
‘(c o p1 A A o k)∶ R → I0 ∧ (c o p2 A A o k)∶ R → I0’ by metis_tac[compose_hom] >>
‘c o p1 A A o k = c o p2 A A o k’ 
  by (‘q' o (c o p1 A A o k) = q' o (c o p2 A A o k)’
      suffices_by metis_tac[is_mono_thm] >>
   ‘(q' ∘ c) ∘ p1 A A ∘ k = (q' ∘ c) ∘ p2 A A ∘ k’
    suffices_by metis_tac[compose_hom,compose_assoc] >>
   ‘f ∘ p1 A A ∘ k = f ∘ p2 A A ∘ k’ suffices_by metis_tac[] >>
   simp[Abbr‘k’] >> metis_tac[eq_equlity,compose_assoc])
   >>
drule coeq_fac_unique >> strip_tac >>
metis_tac[]
QED
  

Theorem Thm3_without_assume_exists:
∀A B f. f∶ A → B ⇒
          ∃!h. h∶ (coeqo ((p1 A A) o (eqa (f o p1 A A) (f o p2 A A)))
                    ((p2 A A) o (eqa (f o p1 A A) (f o p2 A A)))) →
             (eqo ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
                  ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B))) ∧
          (eqa ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
               ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B))) o h o
          (coeqa (p1 A A o (eqa (f o p1 A A) (f o p2 A A)))
                 (p2 A A o (eqa (f o p1 A A) (f o p2 A A))))  = f ∧
          is_iso h
Proof
rw[] >> drule Thm3_h_exists >> simp[EXISTS_UNIQUE_ALT] >> strip_tac >>
qexists_tac ‘h’ >> Cases_on ‘A≅ zero’(*2 *)
>- metis_tac[Thm3_case_zero]
>- metis_tac[Thm3_case_non_zero]
QED



Theorem mono_epi_fac:
∀f A B. f∶ A → B ⇒ ∃X m e. e∶ A → X ∧ m∶ X → B ∧ is_epi m ∧ is_mono e ∧ f = e o m
Proof
rw[] >> drule Thm3_without_assume_exists >> simp[EXISTS_UNIQUE_ALT] >> strip_tac >>
cheat
QED
