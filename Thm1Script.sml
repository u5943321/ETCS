(*
Overload product_obj = “λA B. po A B”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "×"], 
                  term_name = "product_obj", paren_style = OnlyIfNecessary}

Overload exp_notation = “λB A. exp A B”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "^"], 
                  term_name = "exp_notation",
                  paren_style = OnlyIfNecessary}
*)
(*why HOL cannot recognize this notation?*)
          
(*why the three lines does not work...?*)

(*
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, 
                  pp_elements = [TOK "⟨", TM, TOK ",",TM, TOK "⟩"], 
                  term_name = "pa", paren_style = OnlyIfNecessary}
*)                  

                  
Theorem Thm1_case_1_comm_condition_left:
∀B f g. f∶ N → B ∧ g∶ one → B ⇒
          (f o z = g  ⇔ ⟨id N,f⟩ o z = ⟨z,g⟩)
Proof
rw[] >>
‘⟨id N,f⟩∶ N → (N× B) ∧ ⟨z,g⟩∶ one → (N×B) ∧ ⟨id N,f⟩ o z∶ one → (N×B)’
 by metis_tac[id1,pa_hom,compose_hom,ax3] >>
‘z∶ one → N’ by metis_tac[ax3] >>
‘f o z ∶ one → B’ by metis_tac[compose_hom] >>
rw[EQ_IMP_THM] (* 2 *)
>- (irule to_p_eq_applied >> qexistsl_tac [‘N’,‘B’,‘one’] >> rw[] (* 2 *)
   >- (‘p1 N B ∘ ⟨z,f ∘ z⟩ = z’ by metis_tac[p1_of_pa] >>
      ‘p1 N B ∘ ⟨id N,f⟩ ∘ z = (p1 N B ∘ ⟨id N,f⟩) ∘ z’ by metis_tac[compose_assoc,p1_hom] >>
      metis_tac[idL,id1,p1_of_pa])
   >- (‘p2 N B ∘ ⟨z,f ∘ z⟩ = f o z’ by metis_tac[p2_of_pa] >>
      ‘p2 N B ∘ ⟨id N,f⟩ ∘ z = (p2 N B ∘ ⟨id N,f⟩) ∘ z’ by metis_tac[compose_assoc,p2_hom] >>
      metis_tac[idL,id1,p2_of_pa]))
>- (‘p2 N B o ⟨id N,f⟩ ∘ z = p2 N B o ⟨z,g⟩’ by metis_tac[] >>
   ‘p2 N B ∘ ⟨id N,f⟩ ∘ z = (p2 N B ∘ ⟨id N,f⟩) ∘ z’ by metis_tac[compose_assoc,p2_hom] >>
   ‘(p2 N B ∘ ⟨id N,f⟩) = f’ by metis_tac[id1,p2_of_pa] >>
    metis_tac[p2_of_pa])
QED

Theorem Thm1_case_1_comm_condition_right:
∀B f h. f∶ N → B ∧ h∶ N×B → B ⇒
        (h o ⟨id N,f⟩ = f o s ⇔ ⟨s o p1 N B, h⟩ o ⟨id N, f⟩ = ⟨id N, f⟩ o s)
Proof
rw[] >>
‘⟨id N,f⟩∶ N → (N×B)’ by metis_tac[id1,pa_hom] >>
‘h o ⟨id N,f⟩∶ N → B’ by metis_tac[compose_hom] >>
‘s∶ N → N’ by metis_tac[ax3] >>
‘f o s∶ N → B’ by metis_tac[compose_hom] >>
‘⟨id N, f⟩ o s∶ N → (N×B)’ by metis_tac[compose_hom] >>
‘s o p1 N B∶ (N × B) → N’ by metis_tac[compose_hom,p1_hom] >>
‘⟨s o p1 N B, h⟩∶ (N×B) → (N× B)’ by metis_tac[pa_hom] >>
‘⟨s o p1 N B, h⟩ o ⟨id N, f⟩∶ N → (N × B)’ by metis_tac[compose_hom] >>
rw[EQ_IMP_THM] (* 2 *)
>- (irule to_p_eq_applied >> qexistsl_tac [‘N’,‘B’,‘N’] >> rw[] (* 2 *)
   >- (‘p1 N B ∘ ⟨s ∘ p1 N B,h⟩ = s ∘ p1 N B’ by metis_tac[p1_of_pa] >>
      ‘p1 N B ∘ ⟨s ∘ p1 N B,h⟩ ∘ ⟨id N,f⟩ = (p1 N B ∘ ⟨s ∘ p1 N B,h⟩) ∘ ⟨id N,f⟩’
        by metis_tac[compose_assoc,p1_hom] >> rw[] >>
      ‘(s ∘ p1 N B) ∘ ⟨id N,f⟩ =  s ∘ p1 N B ∘ ⟨id N,f⟩’ by metis_tac[compose_assoc,p1_hom] >>
      ‘p1 N B ∘ ⟨id N,f⟩ = id N’ by metis_tac[p1_of_pa,id1] >> rw[] >>
      ‘p1 N B ∘ ⟨id N,f⟩ ∘ s = (p1 N B ∘ ⟨id N,f⟩) ∘ s’ by metis_tac[compose_assoc,p1_hom] >>
      rw[] >> metis_tac[id1,idL,idR])
   >- (‘p2 N B ∘ ⟨s ∘ p1 N B,h⟩ ∘ ⟨id N,f⟩ = (p2 N B ∘ ⟨s ∘ p1 N B,h⟩) ∘ ⟨id N,f⟩’
        by metis_tac[compose_assoc,p2_hom] >>
      ‘(p2 N B ∘ ⟨s ∘ p1 N B,h⟩) = h’ by metis_tac[p2_of_pa] >>
      rw[] >>
      ‘p2 N B ∘ ⟨id N,f⟩ ∘ s = (p2 N B ∘ ⟨id N,f⟩) ∘ s’ by metis_tac[compose_assoc,p2_hom] >>
      ‘(p2 N B ∘ ⟨id N,f⟩) = f’ by metis_tac[id1,p2_of_pa] >>
      metis_tac[]))
>- (‘p2 N B o ⟨s ∘ p1 N B,h⟩ ∘ ⟨id N,f⟩ = p2 N B o ⟨id N,f⟩ ∘ s’ by metis_tac[] >>
   ‘p2 N B o ⟨s ∘ p1 N B,h⟩ ∘ ⟨id N,f⟩ = (p2 N B o ⟨s ∘ p1 N B,h⟩) ∘ ⟨id N,f⟩’
     by metis_tac[compose_assoc,p2_hom] >>
   ‘(p2 N B ∘ ⟨s ∘ p1 N B,h⟩) = h’ by metis_tac[p2_of_pa] >> rw[] >>
   ‘p2 N B ∘ ⟨id N,f⟩ ∘ s = (p2 N B ∘ ⟨id N,f⟩) ∘ s’ by metis_tac[compose_assoc,p2_hom] >>
   ‘(p2 N B ∘ ⟨id N,f⟩) = f’ by metis_tac[id1,p2_of_pa] >>
   metis_tac[])
QED         

Theorem Thm1_case_1:
∀B g h. g∶ one → B ∧ h∶ po N B → B ⇒
        ∃!f. f∶ N → B ∧ f o z = g ∧ f o s = h o ⟨id N, f⟩
Proof
rw[EXISTS_UNIQUE_ALT] >>
‘⟨z,g⟩∶ one → (N× B)’ by metis_tac[ax3,pa_hom] >>
‘⟨s o p1 N B,h⟩∶ (N× B) → (N × B)’ by metis_tac[ax3,pa_hom,p1_hom,compose_hom] >>
drule_all ax3_conj2 >> strip_tac >>
qabbrev_tac ‘f' =  N_ind ⟨z,g⟩ ⟨s ∘ p1 N B,h⟩’ >>
‘f'∶ N → (N × B)’ by metis_tac[] >>
‘p1 N B o f' = id N’
  by (‘p1 N B ∘ f'∶ N → N’ by metis_tac[p1_hom,compose_hom] >>
      irule comm_with_s_id >> reverse (rw[])
      >- (‘p1 N B∶ (N× B) → N’ by metis_tac[p1_hom] >>
         ‘z∶ one → N’ by metis_tac[ax3] >>
         ‘(p1 N B ∘ f') ∘ z = p1 N B ∘ f' ∘ z’ by metis_tac[compose_assoc] >>
         rw[] >>
         ‘p1 N B o ⟨z,g⟩ = z’ suffices_by metis_tac[] >>
         metis_tac[p1_of_pa])
       >>
      ‘f' ∘ s = ⟨s ∘ p1 N B,h⟩ ∘ f'’ by metis_tac[] >>
      ‘p1 N B o f' ∘ s = p1 N B o ⟨s ∘ p1 N B,h⟩ ∘ f'’ by metis_tac[] >>
      ‘p1 N B o f' ∘ s = (p1 N B ∘ f') ∘ s ∧ p1 N B o ⟨s ∘ p1 N B,h⟩ ∘ f' = s ∘ p1 N B ∘ f'’
        suffices_by metis_tac[] >> strip_tac
      >- metis_tac[p1_hom,ax3,compose_assoc]
      >- (‘p1 N B ∘ ⟨s ∘ p1 N B,h⟩ ∘ f' = (p1 N B ∘ ⟨s ∘ p1 N B,h⟩) ∘ f'’
           by metis_tac[p1_hom,ax3,compose_assoc] >>
         rw[] >>
         ‘s ∘ p1 N B ∘ f' = (s ∘ p1 N B) ∘ f'’ by metis_tac[p1_hom,ax3,compose_assoc] >>
         ‘s ∘ p1 N B∶ (N×B) → N’ by metis_tac[compose_hom,ax3,p1_hom] >>
         ‘(p1 N B ∘ ⟨s ∘ p1 N B,h⟩) = s ∘ p1 N B’ by metis_tac[p1_of_pa] >>
         metis_tac[])) (* lemma later  comm_with_s_id *) >>
‘p2 N B o f'∶ N → B’ by metis_tac[p2_hom,compose_hom] >>
qabbrev_tac ‘f = p2 N B o f'’ >>
qexists_tac ‘f’ >>
‘f' = ⟨id N, f⟩’
  by
   (irule to_p_eq_applied >> qexistsl_tac [‘N’,‘B’,‘N’] >>
    ‘⟨id N,f⟩∶N → (N × B)’ by metis_tac[id1,pa_hom] >> rw[] (* 2 *)
    >- metis_tac[p1_of_pa,id1]
    >- metis_tac[p2_of_pa,id1]
   ) >>
 (* lemma later maybe no need for a lemma*)
‘∀f0. f0∶N → B ⇒ (f0 ∘ z = g ∧ f0 ∘ s = h ∘ ⟨id N,f0⟩ ⇔
                 ⟨id N,f0⟩ o z = ⟨z,g⟩ ∧  ⟨s o p1 N B, h⟩ o ⟨id N, f0⟩ = ⟨id N, f0⟩ o s)’
  by metis_tac[Thm1_case_1_comm_condition_left,Thm1_case_1_comm_condition_right] >>
‘f∶N → B ∧ f ∘ z = g ∧ f ∘ s = h ∘ ⟨id N,f⟩ ∧
 ∀f0. f0∶N → B ∧ f0 ∘ z = g ∧ f0 ∘ s = h ∘ ⟨id N,f0⟩ ⇒ f0 = f’ suffices_by metis_tac[] >>
‘∀f0. f0∶N → B ∧ ⟨id N,f0⟩ ∘ z = ⟨z,g⟩ ∧ ⟨id N,f0⟩ ∘ s = ⟨s ∘ p1 N B,h⟩ ∘ ⟨id N,f0⟩ ⇔
      f0 = f’
  by (rw[EQ_IMP_THM] (* 3 *)
     >- (‘⟨id N,f0⟩∶ N → (N×B)’ by metis_tac[pa_hom,id1] >>
        ‘⟨id N,f0⟩ = ⟨id N,f⟩’ by metis_tac[] >>
        metis_tac[to_p_eq_one_side])
     >- metis_tac[]
     >- metis_tac[]) >>
metis_tac[]     
QED
                
Theorem Thm1_comm_eq_left:
∀A B f g. g∶ A → B ∧ f∶ A×N → B ⇒
          (tp f o z = tp (g o (p1 A one)) ⇔
           f o ⟨p1 A one, z o (p2 A one)⟩ = g o (p1 A one))
Proof
rw[] >>
‘tp f∶ N → exp A B’ by metis_tac[tp_hom] >>
‘z∶ one → N’ by metis_tac[ax3] >>
‘tp f o z ∶ one → exp A B’ by metis_tac[compose_hom] >>
‘ (p1 A one)∶ (A× one) → A ∧  (p2 A one)∶ (A × one) → one’ by metis_tac[p1_hom,p2_hom] >>
‘g o (p1 A one)∶ (A × one) → B’ by metis_tac[compose_hom] >>
‘tp (g o (p1 A one))∶ one → exp A B’ by metis_tac[tp_hom] >>
‘z o (p2 A one)∶ (A× one) → N’ by metis_tac[compose_hom] >>
‘⟨p1 A one, z o (p2 A one)⟩∶ (A× one) → (A× N)’ by metis_tac[pa_hom] >>
‘f o ⟨p1 A one, z o (p2 A one)⟩∶ (A×one)→ B’ by metis_tac[compose_hom] >>
‘g o (p1 A one)∶ (A×one)→ B’ by metis_tac[compose_hom] >>
rw[EQ_IMP_THM] (* 2 *)
>- (‘ev A B o ⟨p1 A one, (tp f ∘ z) o p2 A one⟩ = ev A B o ⟨p1 A one, (tp (g ∘ p1 A one)) o p2 A one⟩’
     by metis_tac[] >>
   ‘ev A B ∘ ⟨p1 A one,(tp f ∘ z) ∘ p2 A one⟩ = f ∘ ⟨p1 A one,z ∘ p2 A one⟩  ∧
    ev A B ∘ ⟨p1 A one,tp (g ∘ p1 A one) ∘ p2 A one⟩ =  g ∘ p1 A one’ suffices_by metis_tac[] >>
   strip_tac
   >- (‘(tp f ∘ z) ∘ p2 A one = tp f ∘ z ∘ p2 A one’ by metis_tac[compose_assoc] >>
      ‘⟨p1 A one,(tp f ∘ z) ∘ p2 A one⟩ =  ⟨p1 A one, tp f ∘ z ∘ p2 A one⟩’ by metis_tac[] >>
      ‘⟨p1 A one, tp f ∘ z ∘ p2 A one⟩ = ⟨p1 A N, tp f ∘ p2 A N⟩ o ⟨p1 A one, z ∘ p2 A one⟩’
        by 
         (irule parallel_p_one_side >> metis_tac[]) >>
      ‘ev A B ∘ ⟨p1 A one,(tp f ∘ z) ∘ p2 A one⟩ =
      ev A B o ⟨p1 A N,tp f ∘ p2 A N⟩ ∘ ⟨p1 A one,z ∘ p2 A one⟩’ by metis_tac[] >>
      ‘⟨p1 A N,tp f ∘ p2 A N⟩∶ (A×N) → (A × (exp A B))’
        by metis_tac[pa_hom,p1_hom,p2_hom,compose_hom] >>
      ‘⟨p1 A one,z ∘ p2 A one⟩∶ (A×one)→ (A×N)’ by metis_tac[pa_hom,p1_hom,p2_hom,compose_hom] >>
      ‘ev A B∶ (A× (exp A B))→ B’ by metis_tac[ev_hom] >>
      ‘ev A B o ⟨p1 A N,tp f ∘ p2 A N⟩ ∘ ⟨p1 A one,z ∘ p2 A one⟩ =
      (ev A B o ⟨p1 A N,tp f ∘ p2 A N⟩) ∘ ⟨p1 A one,z ∘ p2 A one⟩’ by metis_tac[compose_assoc] >>
      ‘(ev A B ∘ ⟨p1 A N,tp f ∘ p2 A N⟩) = f’ by metis_tac[ev_of_tp] >>
      metis_tac[])
   >- metis_tac[ev_of_tp])
>- (irule ev_eq_eq >> qexistsl_tac [‘A’,‘B’,‘one’] >> rw[] >>
   ‘(tp f ∘ z) ∘ p2 A one = tp f ∘ z ∘ p2 A one’ by metis_tac[compose_assoc] >>
   ‘⟨p1 A one,(tp f ∘ z) ∘ p2 A one⟩ =  ⟨p1 A one, tp f ∘ z ∘ p2 A one⟩’ by metis_tac[] >>
   ‘⟨p1 A one, tp f ∘ z ∘ p2 A one⟩ = ⟨p1 A N, tp f ∘ p2 A N⟩ o ⟨p1 A one, z ∘ p2 A one⟩’
        by 
         (irule parallel_p_one_side >> metis_tac[]) >>
   ‘ev A B ∘ ⟨p1 A one,(tp f ∘ z) ∘ p2 A one⟩ =
    ev A B o ⟨p1 A N,tp f ∘ p2 A N⟩ ∘ ⟨p1 A one,z ∘ p2 A one⟩’ by metis_tac[] >>
   ‘⟨p1 A N,tp f ∘ p2 A N⟩∶ (A×N) → (A × (exp A B))’
      by metis_tac[pa_hom,p1_hom,p2_hom,compose_hom] >>
   ‘⟨p1 A one,z ∘ p2 A one⟩∶ (A×one)→ (A×N)’ by metis_tac[pa_hom,p1_hom,p2_hom,compose_hom] >>
   ‘ev A B∶ (A× (exp A B))→ B’ by metis_tac[ev_hom] >>
   ‘ev A B o ⟨p1 A N,tp f ∘ p2 A N⟩ ∘ ⟨p1 A one,z ∘ p2 A one⟩ =
    (ev A B o ⟨p1 A N,tp f ∘ p2 A N⟩) ∘ ⟨p1 A one,z ∘ p2 A one⟩’ by metis_tac[compose_assoc] >>
   ‘(ev A B ∘ ⟨p1 A N,tp f ∘ p2 A N⟩) = f’ by metis_tac[ev_of_tp] >>
   rw[] >> metis_tac[ev_of_tp])
QED

Theorem Thm1_comm_eq_right:
∀A B f h. f∶ A× N → B ∧ h∶ (A×N)×B → B ⇒
          (h o ⟨id (A×N), f⟩ = f o ⟨p1 A N, s o (p2 A N)⟩ ⇔
           tp (h o
                ⟨⟨p1 A (N×(exp A B))
                  ,(p1 N (exp A B)) o (p2 A (N×(exp A B)))⟩,
                (ev A B) o ⟨p1 A (N×(exp A B)),
                            (p2 N (exp A B) o (p2 A (N×(exp A B))))⟩⟩

           ) o  ⟨id N,tp f⟩
        = (tp f o s))
Proof 
rw[] >> 
qabbrev_tac ‘l = ⟨⟨p1 A (N×(exp A B)),p1 N (exp A B) ∘ p2 A (N×(exp A B))⟩,ev A B ∘
           ⟨p1 A (N×(exp A B)),p2 N (exp A B) ∘ p2 A (N×(exp A B))⟩⟩’ >>
‘id (A× N)∶ (A× N)→ (A×N)’ by metis_tac[id1] >>
‘⟨id (A×N),f⟩∶ A× N → ((A×N)× B)’ by metis_tac[pa_hom] >>
‘p1 A (N × exp A B)∶ (A × ((N × exp A B))) → A’ by metis_tac[p1_hom]>>
‘p2 A (N × exp A B)∶ (A × ((N × exp A B))) → (N × exp A B)’
  by metis_tac[p2_hom] >>
‘p1 N (exp A B)∶ (N × exp A B) → N’ by metis_tac[p1_hom] >>
‘p2 N (exp A B)∶ (N × exp A B) → exp A B’ by metis_tac[p2_hom] >>
‘p2 N (exp A B) ∘ p2 A (N × exp A B)∶ (A × ((N × exp A B))) → exp A B’ by metis_tac[compose_hom]>>
‘p1 N (exp A B) ∘ p2 A (N × exp A B)∶ (A × ((N × exp A B))) → N’ by metis_tac[compose_hom] >>
‘⟨p1 A (N × exp A B),p1 N (exp A B) ∘ p2 A (N × exp A B)⟩∶ (A × ((N × exp A B))) → (A×N)’
  by metis_tac[pa_hom] >>
‘⟨p1 A (N × exp A B),p2 N (exp A B) ∘ p2 A (N × exp A B)⟩∶ (A × ((N × exp A B))) → (A× (exp A B))’
  by metis_tac[pa_hom] >>
‘ev A B ∘ ⟨p1 A (N × exp A B),p2 N (exp A B) ∘ p2 A (N × exp A B)⟩∶ (A × ((N × exp A B))) → B’
  by metis_tac[ev_hom,compose_hom] >> 
‘(h ∘ ⟨id (A×N),f⟩)∶ A×N → B’ by metis_tac[compose_hom] >>
‘l∶ (A × ((N × exp A B))) → ((A×N)× B)’
  by (simp[Abbr‘l’] >> metis_tac[pa_hom]) >>
‘h o l∶ (A × ((N × exp A B))) → B’ by metis_tac[compose_hom] >>
‘tp f∶ N → exp A B’ by metis_tac[tp_hom] >>
‘⟨id N,tp f⟩∶ N → (N× (exp A B))’ by metis_tac[pa_hom,id1] >>
‘tp (h ∘ l) ∘ ⟨id N,tp f⟩ ∶ N → exp A B’ by metis_tac[tp_hom,compose_hom] >>
‘p1 A N∶ A× N → A’ by metis_tac[p1_hom] >>
‘p2 A N∶ A× N → N’ by metis_tac[p2_hom] >>
‘s o (p2 A N)∶ A× N → N’ by metis_tac[compose_hom,ax3] >>
‘⟨p1 A N,s ∘ p2 A N⟩∶A× N→ (A × N)’ by metis_tac[pa_hom] >> 
‘f ∘ ⟨p1 A N,s ∘ p2 A N⟩∶ A × N → B’ by metis_tac[compose_hom] >>    
‘tp (h ∘ l) ∘ ⟨id N,tp f⟩ = tp (h ∘ ⟨id (A×N),f⟩) ∧
 tp (f ∘ ⟨p1 A N,s ∘ p2 A N⟩) = tp f o s’
 suffices_by metis_tac[tp_eq] >> strip_tac (* 2 *) >- 
(* tp (h ∘ l) ∘ ⟨id N,tp f⟩ = tp (h ∘ ⟨id (A × N),f⟩)*)
(irule is_tp >> qexistsl_tac [‘A’,‘B’,‘N’] >>
‘tp (h o l)∶ (N × exp A B) → exp A B’ by metis_tac[tp_hom] >>
‘p2 A N∶ (A×N) → N’ by metis_tac[p2_hom] >>
‘(tp (h ∘ l) ∘ ⟨id N,tp f⟩) ∘ p2 A N = tp (h ∘ l) ∘ ⟨id N,tp f⟩ ∘ p2 A N’
   by metis_tac[compose_assoc] >> 
‘⟨p1 A N,(tp (h ∘ l) ∘ ⟨id N,tp f⟩) ∘ p2 A N⟩ =
 ⟨p1 A (N× (exp A B)), (tp (h ∘ l)) o p2 A (N× (exp A B))⟩ o
 ⟨p1 A N, ⟨id N,tp f⟩ o p2 A N⟩’
  by
   (simp[] >>irule parallel_p_one_side >> metis_tac[]) >>
 (*lemma for this pattern parallel_p_one_side*) 
simp[] >>
‘ev A B ∘ ⟨p1 A (N×(exp A B)),tp (h ∘ l) ∘ p2 A (N×(exp A B))⟩ = h o l’
  by metis_tac[ev_of_tp] >>
‘⟨id N,tp f⟩ ∘ p2 A N∶ (A×N) → (N× (exp A B))’ by metis_tac[compose_hom] >>
‘⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩∶(A× N) → (A× (N× (exp A B)))’ by metis_tac[pa_hom] >>
‘ev A B∶A × exp A B → B’ by metis_tac[ev_hom] >>
‘⟨p1 A (N × exp A B),tp (h ∘ l) ∘ p2 A (N × exp A B)⟩∶A × (N × exp A B) →  (A × exp A B)’
  by metis_tac[compose_hom,pa_hom] >>
‘ev A B ∘ ⟨p1 A (N×(exp A B)),tp (h ∘ l) ∘ p2 A (N×(exp A B))⟩ ∘
        ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
 (ev A B ∘ ⟨p1 A (N×(exp A B)),tp (h ∘ l) ∘ p2 A (N×(exp A B))⟩) ∘
        ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩’
   by metis_tac[compose_assoc] >> 
‘l o ⟨p1 A N,⟨id N,tp f⟩ o p2 A N⟩ =  ⟨id (A×N),f⟩’
  suffices_by
    (fs[] >> strip_tac >>
    ‘(h ∘ l) ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩  = h ∘ l ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩’
      by metis_tac[compose_assoc] >> metis_tac[]) >> 
‘l ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩∶ A× N → ((A×N)×B )∧
 ⟨id (A×N),f⟩∶ A×N → ((A×N)×B)’
  by (rw[] >> metis_tac[pa_hom,compose_hom]) >>
(*lemma on equality between iterated product iterated_p_eq_applied *)
irule iterated_p_eq_applied >>
qexistsl_tac [‘A’,‘N’,‘B’,‘A×N’] >> rw[] (* 3 *)
>- (‘(p1 (A×N) B) o l =
    ⟨p1 A (N×(exp A B)),p1 N (exp A B) ∘ p2 A (N×(exp A B))⟩’
     by
      (simp[Abbr‘l’] >> metis_tac[p1_of_pa]) >>
   ‘(p1 A N) o ⟨p1 A (N×(exp A B)),p1 N (exp A B) ∘ p2 A (N×(exp A B))⟩=
     p1 A (N×(exp A B))’
     by metis_tac[p1_of_pa] >> 
   ‘(p1 A (N×(exp A B))) o ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
        p1 A N ∘ p1 (A×N) B ∘ ⟨id (A×N),f⟩’
      suffices_by
        (rw[] >>
         ‘p1 (A × N) B ∘ l ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
          (p1 (A × N) B ∘ l) ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩’
           by metis_tac[compose_assoc_SYM,p1_hom] >>
          rw[] >>
         ‘p1 A N ∘ ⟨p1 A (N × exp A B),p1 N (exp A B) ∘ p2 A (N × exp A B)⟩ ∘
        ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
         (p1 A N ∘ ⟨p1 A (N × exp A B),p1 N (exp A B) ∘ p2 A (N × exp A B)⟩) ∘
        ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩’ by metis_tac[compose_assoc_SYM,p1_hom] >>
          rw[]) >>
   ‘p1 (A × N) B ∘ ⟨id (A × N),f⟩ = id (A × N)’ by metis_tac[id1,p1_of_pa] >> rw[] >>
   ‘p1 A N ∘ id (A × N) = p1 A N’ by metis_tac[idR] >>
   ‘p1 A (N × exp A B) ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ = p1 A N’ by metis_tac[id1,p1_of_pa] >>
   rw[]) (*1 out of 3*)
   (*LHS = RHS = p1 A N*) 
>- (‘(p1 (A×N) B) o l =
    ⟨p1 A (N×(exp A B)),p1 N (exp A B) ∘ p2 A (N×(exp A B))⟩’
     by
      (simp[Abbr‘l’] >> metis_tac[p1_of_pa]) >>
   ‘(p2 A N) o ⟨p1 A (N×(exp A B)),p1 N (exp A B) ∘ p2 A (N×(exp A B))⟩=
    p1 N (exp A B) ∘ p2 A (N×(exp A B))’
     by metis_tac[p2_of_pa] >> 
   ‘p1 (A × N) B ∘ l ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
    (p1 (A × N) B ∘ l) ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩’ by metis_tac[compose_assoc,p1_hom] >>
   rw[] >>
   ‘p2 A N ∘ ⟨p1 A (N × exp A B),p1 N (exp A B) ∘ p2 A (N × exp A B)⟩ ∘
        ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
    (p2 A N ∘ ⟨p1 A (N × exp A B),p1 N (exp A B) ∘ p2 A (N × exp A B)⟩) ∘
        ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩’ by metis_tac[compose_assoc,p1_hom] >>
   ‘p2 A N ∘ ⟨p1 A (N × exp A B),p1 N (exp A B) ∘ p2 A (N × exp A B)⟩ =
    p1 N (exp A B) ∘ p2 A (N × exp A B)’ by metis_tac[p2_of_pa] >>
   rw[] >>
   ‘(p1 N (exp A B) ∘ p2 A (N × exp A B)) ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩  =
    p1 N (exp A B) ∘ p2 A (N × exp A B) ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩’
     by metis_tac[compose_assoc,p1_hom] >>
   rw[] >>
   ‘p2 A (N × exp A B) ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ = ⟨id N,tp f⟩ ∘ p2 A N’
     by metis_tac[p2_of_pa,id1] >> rw[] >>
   ‘p1 N (exp A B) ∘ ⟨id N,tp f⟩ ∘ p2 A N = (p1 N (exp A B) ∘ ⟨id N,tp f⟩) ∘ p2 A N’
     by metis_tac[compose_assoc,p1_hom] >>
   ‘(p1 N (exp A B) ∘ ⟨id N,tp f⟩) = id N’ by metis_tac[p1_of_pa,id1] >>
   metis_tac[p1_of_pa,p2_of_pa,idL,idR])
   (*p2 A N 2 out of 3*)   
>- (‘p2 (A×N) B ∘ l =
    ev A B ∘
           ⟨p1 A (N×(exp A B)),p2 N (exp A B) ∘ p2 A (N×(exp A B))⟩’
     by (simp[Abbr‘l’] >> metis_tac[p2_of_pa]) >>
   ‘p2 (A×N) B ∘ l ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ = f’
     suffices_by
      (rw[] >> metis_tac[p2_of_pa]) >>
   ‘p2 (A × N) B ∘ l ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
   (p2 (A × N) B ∘ l) ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ ’
    by (irule compose_assoc_SYM >> metis_tac[p2_hom]) >> rw[] >>
   ‘⟨p1 A (N×exp A B),p2 N (exp A B) ∘ p2 A (N×exp A B)⟩ ∘
        ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩∶ (A×N) → (A× (exp A B)) ∧ 
    ⟨p1 A N,tp f ∘ p2 A N⟩∶(A×N) → (A× (exp A B))’
     by
      (rw[] (* 2 same *) >>
       metis_tac[id1,p1_hom,p2_hom,pa_hom,compose_hom]) >>
   ‘⟨p1 A (N×exp A B),p2 N (exp A B) ∘ p2 A (N×exp A B)⟩ o
    ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩  =
    ⟨p1 A N,(tp f) o p2 A N⟩’
     by
      (irule to_p_eq_applied >>
      qexistsl_tac [‘A’,‘exp A B’,‘A×N’] >> rw[] (* 2 *)
      >- (‘p1 A (exp A B) ∘ ⟨p1 A N,tp f ∘ p2 A N⟩ = p1 A N’
           by (irule p1_of_pa >> metis_tac[p1_hom,p2_hom,compose_hom]) >>
          rw[] >>
          ‘p1 A (exp A B) ∘
             ⟨p1 A (N × exp A B),p2 N (exp A B) ∘ p2 A (N × exp A B)⟩ ∘
             ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
           (p1 A (exp A B) ∘
             ⟨p1 A (N × exp A B),p2 N (exp A B) ∘ p2 A (N × exp A B)⟩) ∘
             ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩’
            by (irule compose_assoc_SYM >> metis_tac[p1_hom]) >>
          rw[] >>
          ‘p1 A (exp A B) ∘
           ⟨p1 A (N × exp A B),p2 N (exp A B) ∘ p2 A (N × exp A B)⟩ = p1 A (N × exp A B)’
           by metis_tac[p1_of_pa,p1_hom,p2_hom] >>
          rw[] >> 
          metis_tac[p1_of_pa,p1_hom,p2_hom]  
           )
          (*p1 A N 1 out of 2*)
      >- (*RHS (tp f ∘ p2 A N)   LHS ... *)
          (‘p2 A (exp A B) ∘ ⟨p1 A (N×exp A B),p2 N (exp A B) ∘ p2 A (N×exp A B)⟩ =
           p2 N (exp A B) ∘ p2 A (N×exp A B)’
            by metis_tac[p2_of_pa,p1_hom,p2_hom] >> 
          ‘p2 N (exp A B) ∘ p2 A (N×exp A B) o ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
           (tp f ∘ p2 A N)’
           suffices_by
            (rw[] >>
             ‘p2 A (exp A B) ∘ ⟨p1 A N,tp f ∘ p2 A N⟩ = tp f ∘ p2 A N’
               by metis_tac[p1_hom,p2_hom,p2_of_pa,compose_hom] >>
             ‘p2 A (exp A B) ∘ ⟨p1 A (N × exp A B),p2 N (exp A B) ∘ p2 A (N × exp A B)⟩ ∘
              ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
               (p2 A (exp A B) ∘
                ⟨p1 A (N × exp A B),p2 N (exp A B) ∘ p2 A (N × exp A B)⟩) ∘
               ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩’
               by (irule compose_assoc_SYM >> metis_tac[p2_hom]) >>
              rw[] >>
              ‘(p2 N (exp A B) ∘ p2 A (N × exp A B)) ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
               p2 N (exp A B) ∘ p2 A (N × exp A B) ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩’
               suffices_by metis_tac[] >>
             metis_tac[compose_assoc]) (*end of suffices*) >>
           ‘p2 A (N × exp A B) ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ = ⟨id N,tp f⟩ ∘ p2 A N’
             by metis_tac[p2_of_pa,p1_hom,p2_hom] >> rw[] >>
           ‘p2 N (exp A B) ∘ ⟨id N,tp f⟩ ∘ p2 A N =  (p2 N (exp A B) ∘ ⟨id N,tp f⟩) ∘ p2 A N’
             by (irule compose_assoc_SYM >> metis_tac[p2_of_pa,p2_hom,compose_hom,pa_hom,id1]) >>
           ‘(p2 N (exp A B) ∘ ⟨id N,tp f⟩) = tp f’ by metis_tac[p2_of_pa,p2_hom,id1] >>
           rw[])) >>
            (*end of thebig by tactic*)
    ‘(ev A B ∘ ⟨p1 A (N × exp A B),p2 N (exp A B) ∘ p2 A (N × exp A B)⟩) ∘
        ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
     ev A B ∘ ⟨p1 A (N × exp A B),p2 N (exp A B) ∘ p2 A (N × exp A B)⟩ ∘
        ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩’
      by (irule compose_assoc >> metis_tac[p2_of_pa,p2_hom,compose_hom,pa_hom,id1]) >>
    rw[] >> metis_tac[ev_of_tp]))     >>          
(*match the two big case dividing*)
(*tp (f ∘ ⟨p1 A N,s ∘ p2 A N⟩) = tp f ∘ s*)  
‘(tp f o s)∶ N → exp A B’ by metis_tac[ax3,compose_hom] >>
‘tp (f ∘ ⟨p1 A N,s ∘ p2 A N⟩) ∶ N → exp A B’ by metis_tac[tp_hom] >>
‘(ev A B) o ⟨p1 A N,(tp f ∘ s) ∘ p2 A N⟩ = (f ∘ ⟨p1 A N,s ∘ p2 A N⟩)’
     suffices_by
       (strip_tac >> simp[EQ_SYM_EQ] >> irule is_tp >>
        qexistsl_tac [‘A’,‘B’,‘N’] >> rw[]) >>
‘⟨p1 A N,(tp f ∘ s) ∘ p2 A N⟩ =
 ⟨p1 A N, (tp f) o (p2 A N)⟩ o ⟨p1 A N, s o (p2 A N)⟩’
 by
  (irule parallel_p_one_side' >> metis_tac[ax3]) >>
rw[] >>
‘⟨p1 A N,s ∘ p2 A N⟩∶(A × N) → (A × N)’ by metis_tac[p1_hom,p2_hom,pa_hom,compose_hom,ax3] >>
‘⟨p1 A N,tp f ∘ p2 A N⟩∶(A×N) → (A×(exp A B))’ by metis_tac[pa_hom,compose_hom,p1_hom,p2_hom] >> 
‘ev A B ∘ ⟨p1 A N,tp f ∘ p2 A N⟩ ∘ ⟨p1 A N,s ∘ p2 A N⟩ =
 (ev A B ∘ ⟨p1 A N,tp f ∘ p2 A N⟩) ∘ ⟨p1 A N,s ∘ p2 A N⟩’
by (irule compose_assoc_SYM >> metis_tac[ev_hom]) >> 
rw[] >>
‘(ev A B ∘ ⟨p1 A N,tp f ∘ p2 A N⟩) = f’ by metis_tac[ev_of_tp] >>
metis_tac[]
QED        


Theorem Thm1_comm_eq_condition:
∀A B f g h. g∶ A → B ∧ h∶ (po (po A N) B) → B ∧ f∶ po A N → B ⇒
       ((f o ⟨p1 A one, z o (p2 A one)⟩ = g o (p1 A one) ∧
        h o ⟨id (po A N), f⟩ = f o ⟨p1 A N, s o (p2 A N)⟩) ⇔
        (tp f o z = tp (g o (p1 A one)) ∧
        tp (h o ⟨
                 ⟨p1 A (po N (exp A B)),
                  (p1 N (exp A B)) o p2 A (po N (exp A B))
                 ⟩,
                 (ev A B) o
                 ⟨p1 A (po N (exp A B)), (p2 N (exp A B)) o p2 A (po N (exp A B))⟩⟩) o
         ⟨id N, tp f⟩ = (tp f) o s))
Proof
metis_tac[Thm1_comm_eq_left,Thm1_comm_eq_right]
QED        
        
Theorem Thm_1:
∀g h A B. g∶ A → B ∧ h∶ (po (po A N) B) → B ⇒
          ∃!f. f∶ po A N → B ∧
               f o ⟨p1 A one, z o (p2 A one)⟩ = g o (p1 A one) ∧
               h o ⟨id (po A N), f⟩ = f o ⟨p1 A N, s o (p2 A N)⟩
Proof
rw[] >>
qabbrev_tac ‘g' = tp (g o (p1 A one))’ >>
qabbrev_tac ‘h' = tp (h o
                      ⟨⟨p1 A (po N (exp A B)), (p1 N (exp A B)) o p2 A (po N (exp A B))⟩,
                      (ev A B) o
                      ⟨p1 A (po N (exp A B)), (p2 N (exp A B)) o p2 A (po N (exp A B))⟩⟩)’>>
‘p1 A one∶ (A×one)→ A’ by metis_tac[p1_hom] >>
‘g o p1 A one∶ (A×one) → B’ by metis_tac[compose_hom] >>                
‘g'∶ one → exp A B’ by (simp[Abbr‘g'’] >> metis_tac[tp_hom]) >>
rw[] >> 
qabbrev_tac ‘l = ⟨⟨p1 A (N×(exp A B)),p1 N (exp A B) ∘ p2 A (N×(exp A B))⟩,ev A B ∘
           ⟨p1 A (N×(exp A B)),p2 N (exp A B) ∘ p2 A (N×(exp A B))⟩⟩’ >>
‘id (A× N)∶ (A× N)→ (A×N)’ by metis_tac[id1] >>
‘p1 A (N × exp A B)∶ (A × ((N × exp A B))) → A’ by metis_tac[p1_hom]>>
‘p2 A (N × exp A B)∶ (A × ((N × exp A B))) → (N × exp A B)’
  by metis_tac[p2_hom] >>
‘p1 N (exp A B)∶ (N × exp A B) → N’ by metis_tac[p1_hom] >>
‘p2 N (exp A B)∶ (N × exp A B) → exp A B’ by metis_tac[p2_hom] >>
‘p2 N (exp A B) ∘ p2 A (N × exp A B)∶ (A × ((N × exp A B))) → exp A B’ by metis_tac[compose_hom]>>
‘p1 N (exp A B) ∘ p2 A (N × exp A B)∶ (A × ((N × exp A B))) → N’ by metis_tac[compose_hom] >>
‘⟨p1 A (N × exp A B),p1 N (exp A B) ∘ p2 A (N × exp A B)⟩∶ (A × ((N × exp A B))) → (A×N)’
  by metis_tac[pa_hom] >>
‘⟨p1 A (N × exp A B),p2 N (exp A B) ∘ p2 A (N × exp A B)⟩∶ (A × ((N × exp A B))) → (A× (exp A B))’
  by metis_tac[pa_hom] >>
‘ev A B ∘ ⟨p1 A (N × exp A B),p2 N (exp A B) ∘ p2 A (N × exp A B)⟩∶ (A × ((N × exp A B))) → B’
  by metis_tac[ev_hom,compose_hom] >> 
‘l∶ (A × ((N × exp A B))) → ((A×N)× B)’
  by (simp[Abbr‘l’] >> metis_tac[pa_hom]) >>
‘h o l∶ (A × ((N × exp A B))) → B’ by metis_tac[compose_hom] >>
(*‘tp f∶ N → exp A B’ by metis_tac[tp_hom] >>
‘⟨id N,tp f⟩∶ N → (N× (exp A B))’ by metis_tac[pa_hom,id1] >>
‘tp (h ∘ l) ∘ ⟨id N,tp f⟩ ∶ N → exp A B’ by metis_tac[tp_hom,compose_hom] >>
‘p1 A N∶ A× N → A’ by metis_tac[p1_hom] >>
‘p2 A N∶ A× N → N’ by metis_tac[p2_hom] >>
‘s o (p2 A N)∶ A× N → N’ by metis_tac[compose_hom,ax3] >>
‘⟨p1 A N,s ∘ p2 A N⟩∶A× N→ (A × N)’ by metis_tac[pa_hom] >> 
     
‘’*)
‘h'∶ (N ×(exp A B)) → exp A B’ by (simp[Abbr‘h'’] >> metis_tac[tp_hom]) >>
drule_all Thm1_case_1 >> strip_tac >>
fs[Once EXISTS_UNIQUE_ALT] >>
qexists_tac ‘(ev A B) o ⟨p1 A N, f o (p2 A N)⟩’ >>
‘f∶N → exp A B’ by metis_tac[] >>
rename [‘fb∶ N → exp A B’] >>
qabbrev_tac ‘f = ev A B ∘ ⟨p1 A N,fb ∘ p2 A N⟩’ >>
‘f∶A×N → B’ by (simp[Abbr‘f’] >> metis_tac[ev_of_pair_hom]) >>
simp[EQ_IMP_THM] >> strip_tac >> strip_tac (* 2 *)
>- (rw[] >>
   ‘tp f' ∘ z = tp (g ∘ p1 A one) ∧
          tp
            (h ∘
             ⟨⟨p1 A (N×exp A B),p1 N (exp A B) ∘ p2 A (N×exp A B)⟩,ev A B ∘
             ⟨p1 A (N×exp A B),p2 N (exp A B) ∘ p2 A (N×exp A B)⟩⟩) ∘
          ⟨id N,tp f'⟩ =
          tp f' ∘ s’ by metis_tac[Thm1_comm_eq_condition] >>
    ‘tp (h ∘ l) ∘ ⟨id N,tp f'⟩ =  tp f' ∘ s’ by metis_tac[Abbr‘l’] >>
    ‘tp f' = fb’
      by
       (‘tp f'∶N → exp A B ∧ tp f' ∘ z = g' ∧ tp f' ∘ s = h' ∘ ⟨id N,tp f'⟩’
          suffices_by metis_tac[] >>
        ‘tp f'∶N→ exp A B’ by metis_tac[tp_hom] >>
        ‘tp f' ∘ z = g'’ by metis_tac[Abbr‘g’] >>
        ‘tp f' ∘ s = h' ∘ ⟨id N,tp f'⟩’ by metis_tac[Abbr‘h'’] >>
        metis_tac[]) >>
    ‘tp f = fb’
      by
       (‘tp f∶N → exp A B ∧ tp f ∘ z = g' ∧ tp f ∘ s = h' ∘ ⟨id N,tp f⟩’ suffices_by metis_tac[]>>
        ‘tp f∶N → exp A B’ by metis_tac[tp_hom] >> 
        rpt strip_tac (* 3 *)
        >- rw[]
        >- (rw[Abbr‘f’] >> rw[Abbr‘g'’] >> metis_tac[ev_of_tp])
        >- (rw[Abbr‘f’] >>
            ‘ev A B ∘ ⟨p1 A N,tp f' ∘ p2 A N⟩ = f'’ by metis_tac[ev_of_tp] >>
            rw[] >> rw[Abbr‘h'’])) >>
    metis_tac[tp_eq])
>- (strip_tac >>
   ‘tp f' ∘ z = tp (g ∘ p1 A one) ∧
          tp
            (h ∘
             ⟨⟨p1 A (N×exp A B),p1 N (exp A B) ∘ p2 A (N×exp A B)⟩,ev A B ∘
             ⟨p1 A (N×exp A B),p2 N (exp A B) ∘ p2 A (N×exp A B)⟩⟩) ∘
          ⟨id N,tp f'⟩ =
          tp f' ∘ s’ suffices_by metis_tac[Thm1_comm_eq_condition] >>
    fs[] >>
    ‘tp f = fb’
     by (rw[Abbr‘f’] >>
         ‘fb = tp (ev A B ∘ ⟨p1 A N,fb ∘ p2 A N⟩)’ suffices_by metis_tac[] >>
        irule is_tp >> metis_tac[]) >>
     metis_tac[])
QED    
(*outlined*)
