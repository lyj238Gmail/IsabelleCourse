theory flash49Rev imports flashPub
begin
section{*Main defintions*}
lemma NI_FAckVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_FAck ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Inv  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_1VsInv49:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_InvAck_1  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_InvAck_1_HomeVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_InvAck_1_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_2VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_InvAck_2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_GetXVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_GetX ))     (neg ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv3)) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv2) )   (Const iInv3))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))     (neg ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2)) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak1VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak2VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak3VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX1VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX2VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX3VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX3 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX4VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX4 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX5VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX5 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX6VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX6 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX7VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX7 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX8VsInv49:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX8 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX8_homeVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX8_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX9VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX9 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX10VsInv49:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX10 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX10_homeVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX10_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX11VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX11 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_GetVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_Get_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_GetX ))     (neg ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv3)) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv2) )   (Const iInv3))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))     (neg ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2)) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak1VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak2VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_Get_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak3VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_Get_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put1VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_Get_Put1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put2VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_Get_Put2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put3VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_Get_Put3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_PutVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_PutXAcksDoneVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Local_PutXAcksDone ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_NakVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Nak  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Nak_ClearVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Nak_Clear ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Nak_HomeVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Nak_Home ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_GetX_NakVsInv49:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_GetX_Nak_HomeVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Remote_GetX_Nak_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_GetX_PutXVsInv49:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_GetX_PutX_HomeVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Remote_GetX_PutX_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_Get_Nak1VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Remote_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_Get_Nak2VsInv49:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_Get_Put1VsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Remote_Get_Put1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_Get_Put2VsInv49:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Remote_Get_Put2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_PutVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Remote_Put  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_PutXVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_ReplaceVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceHomeVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_ReplaceHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceHomeShrVldVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_ReplaceHomeShrVld ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceShrVldVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_ReplaceShrVld  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ShWbVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_ShWb N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_WbVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (NI_Wb ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_GetX1VsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Local_GetX_GetX1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_GetX2VsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Local_GetX_GetX2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX1VsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Local_GetX_PutX1 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX2VsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Local_GetX_PutX2 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX3VsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Local_GetX_PutX3 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX4VsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Local_GetX_PutX4 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_Get_GetVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Local_Get_Get ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_Get_PutVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Local_Get_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_PutXVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Local_PutX ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_ReplaceVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Local_Replace ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_GetVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Remote_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Remote_GetXVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Remote_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Remote_PutXVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_ReplaceVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (PI_Remote_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma StoreVsInv49:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (Store  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma StoreHomeVsInv49:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) (StoreHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  end
