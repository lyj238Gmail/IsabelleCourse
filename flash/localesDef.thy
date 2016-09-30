
theory localesDef imports cache
begin

locale pRule0VsPInv0=
  fixes paraRule ::"  rule"  and paraInv::"formula "
  assumes

  b:"
  invHoldForRule' s   (paraInv) (paraRule )  (invariants N) "  
begin
theorem  pRule0VsPInv0:

  shows "invHoldForRule' s   (paraInv) (paraRule  )   (invariants N) " 
  by(cut_tac a1 b,auto)
end


locale pRule0VspInv1=
  fixes paraRule ::"rule"  and paraInv::"nat\<Rightarrow>formula "  
  and iInv1::"nat"   and N::"nat"
  assumes  
  b:"invHoldForRule' s   (paraInv iInv1) (paraRule)  invariants  "  
begin
theorem  pRule10VspInv1:
   assumes a1:"iInv1 \<le> N"  


  shows "invHoldForRule' s   (paraInv iInv1) (paraRule )   invariants  " 
  by(cut_tac a1 b,auto)
end



locale pRule0VsPInv2=
  fixes paraRule ::"  rule"  and paraInv::"nat\<Rightarrow>nat\<Rightarrow>formula "  and iInv1::"nat" and iInv2::"nat" and N::"nat" and  invariants::"formula set"
  assumes  

  b:" invHoldForRule' s  (paraInv iInv1 iInv2) (paraRule)  invariants  "  
begin
theorem  pRule0VsPInv2:
    assumes  a2:" iInv1 \<le> N " and a3:"iInv2 \<le> N "
  and a4:"iInv1 \<noteq> iInv2" 


  shows "invHoldForRule' s  (paraInv iInv1 iInv2) (paraRule )   invariants " 
   
  by(cut_tac a1 b,auto)
end

locale pRule0VsPInv3=
  fixes paraRule ::"  rule"  and paraInv::"nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>formula "  and iInv1::"nat" and iInv2::"nat" 
  and iInv3::"nat"  and N::"nat" and  invariants::"formula set"
  assumes  a2:" iInv1 \<le> N " and a3:"iInv2 \<le> N " and a4:"iInv3 \<le> N "
  and a5:"iInv1 \<noteq> iInv2" and a6:"iInv1 \<noteq> iInv3" and a7:"iInv2 \<noteq> iInv3" and

  b:" invHoldForRule' s  (paraInv iInv1 iInv2 iInv3) (paraRule)  invariants  "  
begin
theorem  pRule0VsPInv2:


  shows "invHoldForRule' s  (paraInv iInv1 iInv2 iInv3) (paraRule )   invariants " 
   
  by(cut_tac  b,auto)
end


locale pRule1VsPInv0=
  fixes paraRule ::"nat \<Rightarrow>  rule"  and paraInv::"formula "  
  and iRule1::"nat"   and N::"nat"  and  invariants::"formula set"
  assumes
  b:"
  invHoldForRule' s   (paraInv) (paraRule iRule1)  invariants "  
begin
theorem  pRule1VsPInv0:
   assumes
  a1:"iRule1 \<le> N "

  shows "invHoldForRule' s   (paraInv) (paraRule iRule1 )   invariants " 
  (is "?P paraInv  paraRule iRule1    invs")
  by(cut_tac a1 b,auto)
end
 


locale pRule1VspInv1=
  fixes paraRule ::"nat \<Rightarrow> rule"  and paraInv::"nat \<Rightarrow> formula "  
  and iRule::"nat" and iInv1::"nat"  and N::"nat"  and  invariants::"formula set"
  assumes 
 
  b:" iRule = iInv1 \<longrightarrow> 
  (invHoldForRule' s   (paraInv iInv1) (paraRule iRule)  invariants )"  and 
  c:"  iRule \<noteq> iInv1 \<longrightarrow> 
  (invHoldForRule' s   (paraInv iInv1) (paraRule iRule)  invariants  )" 
begin
theorem pRule1VspInv1:
  assumes
   a1:"iRule \<le> N"  and a2:" iInv1 \<le> N "
  shows "(invHoldForRule' s   (paraInv iInv1) (paraRule iRule)  invariants  )"
    (is "?P paraInv iInv1 paraRule iRule  invariants")
  proof -
   have e2:"iRule=iInv1  \<or> iRule \<noteq> iInv1 "  by auto
     
     
   moreover
   {assume e3:" iRule=iInv1 "
            
     have "?P paraInv iInv1 paraRule iRule  invariants"
       by (metis a1 a2 b e3)
   }     
   moreover
   {assume e3:"iRule\<noteq>iInv1 "
     have "?P paraInv iInv1 paraRule iRule  invariants "
       by (metis a1 a2 c e3)
   }
   ultimately show "?P paraInv iInv1 paraRule iRule  invariants "
     by blast
 qed
end
  
 locale pRule1VspInv2=
  fixes paraRule ::"nat \<Rightarrow> rule"  and paraInv::"nat \<Rightarrow> nat\<Rightarrow>formula "  
  and iRule::"nat" and iInv1::"nat" and iInv2::"nat" and N::"nat"   and  invariants::"formula set"
  
  assumes
  b:"iRule \<le> N\<longrightarrow> iInv1 \<le> N \<longrightarrow>iInv2 \<le> N\<longrightarrow>iInv1 \<noteq> iInv2 \<longrightarrow> iRule = iInv1\<longrightarrow>
  invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule)  invariants "  and 
  c:"iRule \<le> N\<longrightarrow> iInv1 \<le> N \<longrightarrow>iInv2 \<le> N\<longrightarrow>iInv1 \<noteq> iInv2 \<longrightarrow>iRule = iInv2 \<longrightarrow> 
  invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule) invariants"  and
  d:"iRule \<le> N\<longrightarrow> iInv1 \<le> N \<longrightarrow>iInv2 \<le> N\<longrightarrow>iInv1 \<noteq> iInv2 \<longrightarrow>iRule \<noteq> iInv1 \<longrightarrow>iRule \<noteq> iInv2 \<longrightarrow> 
  invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule)  invariants"
begin
theorem  pRule1VspInv2:
 assumes  a1:"iRule \<le> N"  and a2:" iInv1 \<le> N " and a3:"iInv2 \<le> N "and a4:"iInv1 \<noteq> iInv2" 
  
  shows "invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule)   invariants "  (is "?P paraInv iInv paraRule iRule  invs")
  proof -
   have d2:"iRule=iInv1 \<or> iRule=iInv2 \<or> ((iRule \<noteq> iInv1) \<and> (iRule\<noteq>iInv2))"  by auto
   moreover
   {assume e1:"iRule=iInv1"
     have "?P paraInv iInv paraRule iRule  invs "
       by (metis  a2 a3 a4 b e1)
              
           
   }    
   
   moreover
   {assume e1:"iRule = iInv2"            
     have "?P paraInv iInv paraRule iRule  invs"
       by (metis  a2 a3 a4 c e1)
   }
   
       
   moreover
   {assume e1:"iRule\<noteq>iInv1 \<and> iRule\<noteq>iInv2"
     have "?P paraInv iInv paraRule iRule  invs"
       by (metis  a1 a2 a3 a4 d e1)
            
   }
   ultimately show "?P paraInv iInv paraRule iRule  invs"
     by blast
 qed
end


locale pRule1VspInv3=
  fixes paraRule ::"nat \<Rightarrow> rule"  and paraInv::"nat \<Rightarrow> nat\<Rightarrow>nat\<Rightarrow>formula "  
  and iRule::"nat" and iInv1::"nat" and iInv2::"nat" and iInv3::"nat" and N::"nat"   and  invariants::"formula set" 
  assumes 
  b:"iRule = iInv1 \<longrightarrow> 
  invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule)  invariants "  and 
  c:" iRule = iInv2 \<longrightarrow> 
  invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule) invariants"  and
  d:"  iRule = iInv3 \<longrightarrow>
  invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule)  invariants" and
  
  e:" iRule \<noteq> iInv1 \<longrightarrow>iRule \<noteq> iInv2 \<longrightarrow> iRule \<noteq> iInv3 \<longrightarrow>
  invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule)  invariants"
begin
theorem  pRule1VspInv3:
  assumes a1:"iRule \<le> N"  and a2:" iInv1 \<le> N " and a3:"iInv2 \<le> N " and a4:"iInv3 \<le> N "
  and a5:"iInv1 \<noteq> iInv2"  and a6:"iInv1 \<noteq> iInv3"   and a7:"iInv2 \<noteq> iInv3"
  shows "invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule)   invariants " 
  proof -
   have d2:"iRule=iInv1 \<or> iRule=iInv2 \<or> iRule=iInv3 \<or> ((iRule \<noteq> iInv1) \<and> (iRule\<noteq>iInv2) \<and> iRule \<noteq> iInv3 )"  by auto
   moreover
   {assume e1:"iRule=iInv1"
     have "invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule)   invariants " 
       by (cut_tac b e1, auto)
              
           
   }     
   moreover
   {assume e1:"iRule = iInv2"            
     have "invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule)   invariants " 
       by (cut_tac c e1,auto)
   }
   
       
   moreover
   {assume e1:"iRule = iInv3"
     have "invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule)   invariants " 
       by (cut_tac  d  e1,auto)
            
   }
   
   moreover
   {assume e1:"iRule\<noteq>iInv1 \<and> iRule\<noteq>iInv2 \<and> iRule\<noteq>iInv3"
      have "invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule)   invariants "
      by (metis e e1) 
            
   }
   ultimately show "invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule)   invariants "
     by blast
 qed
end



locale paraRuleInstValidateExLessInvInst=
  fixes paraRule ::"nat \<Rightarrow> rule"  and paraInv::"nat \<Rightarrow> formula "  
  and iRule::"nat" and iInv1::"nat"  and N::"nat"
  assumes  
  b:"iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow> iRule = iInv1 \<longrightarrow> 
  (invHoldForRule' s  (paraInv iInv1) (paraRule iRule)  invariants )"  and 
  c:"iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>  iRule \<noteq> iInv1 \<longrightarrow> 
  (invHoldForRule' s  (paraInv iInv1) (paraRule iRule)  invariants  )" 
begin
theorem paraRuleInstValidateExLessInvInst:
  assumes a1:"iRule \<le> N"  and a2:" iInv1 \<le> N "
  shows "(invHoldForRule' s  (paraInv iInv1) (paraRule iRule)  invariants  )"
    (is "?P paraInv iInv1 paraRule iRule  invariants")
  proof -
   have e2:"iRule=iInv1  \<or> iRule \<noteq> iInv1 "  by auto
     
     
   moreover
   {assume e3:" iRule=iInv1 "
            
     have "?P paraInv iInv1 paraRule iRule  invariants"
       by (metis a1 a2 b e3)
   }     
   moreover
   {assume e3:"iRule\<noteq>iInv1 "
     have "?P paraInv iInv1 paraRule iRule  invariants "
       by (metis a1 a2 c e3)
   }
   ultimately show "?P paraInv iInv1 paraRule iRule  invariants "
     by blast
 qed
end
  
  
locale paraRuleInstValidateExTwoLessInvInst=
  fixes paraRule ::"nat \<Rightarrow> rule"  and paraInv::"nat \<Rightarrow> nat\<Rightarrow>formula "  
  and iRule::"nat" and iInv1::"nat" and iInv2::"nat" and N::"nat"
  assumes  
  b:"iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iInv2 \<le> N\<longrightarrow>iRule = iInv1 \<longrightarrow> 
  invHoldForRule' s  (paraInv iInv1 iInv2) (paraRule iRule)  invariants "  and 
  c:"iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iInv2 \<le> N\<longrightarrow>iRule = iInv2 \<longrightarrow> 
  invHoldForRule' s  (paraInv iInv1 iInv2) (paraRule iRule) invariants"  and
  d:"iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iInv2 \<le> N\<longrightarrow>iRule \<noteq> iInv1 \<longrightarrow>iRule \<noteq> iInv2 \<longrightarrow> 
  invHoldForRule' s  (paraInv iInv1 iInv2) (paraRule iRule)  invariants"
begin
theorem paraRuleInstValidateExTwoLessInvInst:
  assumes a1:"iRule \<le> N"  and a2:" iInv1 \<le> N " and a3:"iInv2 \<le> N "
  and a4:"iInv1 \<noteq> iInv2"
  shows "invHoldForRule' s  (paraInv iInv1 iInv2) (paraRule iRule)   invariants "  (is "?P paraInv iInv paraRule iRule  invs")
  proof -
   have d2:"iRule=iInv1 \<or> iRule=iInv2 \<or> ((iRule \<noteq> iInv1) \<and> (iRule\<noteq>iInv2))"  by auto
   moreover
   {assume e1:"iRule=iInv1"
     have "?P paraInv iInv paraRule iRule  invs "
       by (metis  a2 a3 a4 b e1)
              
           
   }     
   moreover
   {assume e1:"iRule = iInv2"            
     have "?P paraInv iInv paraRule iRule  invs"
       by (metis  a2 a3 a4 c e1)
   }
   
       
   moreover
   {assume e1:"iRule\<noteq>iInv1 \<and> iRule\<noteq>iInv2"
     have "?P paraInv iInv paraRule iRule  invs"
       by (metis  a1 a2 a3 a4 d e1)
            
   }
   ultimately show "?P paraInv iInv paraRule iRule  invs"
     by blast
 qed
end



locale pRule2VsPInv0=
  fixes paraRule ::"nat \<Rightarrow> nat\<Rightarrow> rule"  and paraInv::"formula "  
  and iRule1::"nat" and iRule2::"nat"  and N::"nat"
  assumes

  b:"
  invHoldForRule' s   (paraInv) (paraRule iRule1 iRule2)  invariants "  
begin
theorem  pRule12sPInv0:
  assumes a1:"iRule1 \<le> N"  and a2:"iRule2 \<le>N"

  shows "invHoldForRule' s   (paraInv) (paraRule iRule1 iRule2)   invariants " 
 
  by(cut_tac a1 a2 b,auto)
end
 


locale pRule2VspInv1=
  fixes paraRule ::"nat \<Rightarrow>nat\<Rightarrow> rule"  and paraInv::"nat \<Rightarrow> formula "  
  and iRule1::"nat" and iRule2::"nat" and iInv1::"nat"  and N::"nat"
  assumes 
  b:" iRule1 = iInv1 \<longrightarrow> 
  (invHoldForRule' s   (paraInv iInv1) (paraRule iRule1  iRule2)  invariants )"  and 
  c:"  iRule2= iInv1  \<longrightarrow>
  (invHoldForRule' s   (paraInv iInv1) (paraRule iRule1  iRule2)  invariants  )"   and 
  d:"  iRule1\<noteq> iInv1  \<longrightarrow>iRule2\<noteq> iInv1 \<longrightarrow>
  (invHoldForRule' s   (paraInv iInv1) (paraRule iRule1  iRule2)  invariants  )"  
begin
theorem pRule2VspInv1:
  assumes a1:"iRule1 \<le> N"  and a2:" iRule2 \<le> N " and a3:" iInv1 \<le> N "
  shows "(invHoldForRule' s   (paraInv iInv1) (paraRule  iRule1  iRule2)  invariants  )" 
  proof -
   have e2:"iRule1=iInv1  \<or> iRule2 = iInv1 \<or> (iRule1\<noteq> iInv1  \<and> iRule2\<noteq> iInv1) "  by auto
     
     
   moreover
   {assume e3:" iRule1=iInv1 "
            
     have "(invHoldForRule' s   (paraInv iInv1) (paraRule  iRule1  iRule2)  invariants  )" 
       by (cut_tac b e3,auto )
   }     
   moreover
   {assume e3:" iRule2=iInv1 "
            
     have "(invHoldForRule' s   (paraInv iInv1) (paraRule  iRule1  iRule2)  invariants  )" 
       by (cut_tac c e3,auto )
   }
    moreover
   {assume e3:" (iRule1\<noteq> iInv1  \<and> iRule2\<noteq> iInv1) "
            
     have "(invHoldForRule' s   (paraInv iInv1) (paraRule  iRule1  iRule2)  invariants  )" 
       by (cut_tac d e3,auto )
   }
   ultimately show"(invHoldForRule' s   (paraInv iInv1) (paraRule  iRule1  iRule2)  invariants  )" 
     by blast
 qed
end
  

locale pRule2VsPInv2=
  fixes paraRule ::"nat \<Rightarrow> nat\<Rightarrow>rule"  and paraInv::"nat \<Rightarrow> nat\<Rightarrow>formula "  
  and iRule1::"nat" and iRule2::"nat"  and iInv1::"nat" and iInv2::"nat" and N::"nat" and invariants::"formula set"
  assumes
  b:"iRule1 = iInv1 \<and> iRule2 = iInv2\<longrightarrow>
  invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule1 iRule2)  invariants "  and 
  c:"iRule1 = iInv1 \<and> iRule2 \<noteq> iInv2\<longrightarrow>
  invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule1 iRule2)  invariants "  and
  d:"iRule1 = iInv2 \<longrightarrow>  
  invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule1 iRule2) invariants"  and
  e:"iRule1 \<noteq> iInv2 \<longrightarrow> 
  invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule1 iRule2)  invariants"   
begin
theorem  pRule1VspInv2:
  assumes a1:"iRule \<le> N"  and a2:" iInv1 \<le> N " and a3:"iInv2 \<le> N "
  and a4:"iInv1 \<noteq> iInv2"
  shows "invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule1 iRule2)   invariants "
  proof -
   have d2:"(iRule1 = iInv1 \<and> iRule2 = iInv2)\<and> (iRule1 = iInv1 \<and> iRule2 \<noteq> iInv2) \<or> iRule1=iInv2 \<or> ( (iRule1\<noteq>iInv2))"  by auto
   moreover
   {assume e1:"iRule1=iInv1 \<and> iRule2 = iInv2"
     have "invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule1 iRule2)   invariants "
       by (cut_tac b e1,auto)
              
           
   }     
   moreover
   {assume e1:"iRule1 = iInv1 \<and> iRule2 \<noteq> iInv2"            
     have "invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule1 iRule2)   invariants "
       by (metis  a2 a3 a4 c e1)
   }
   
       
   moreover
   {assume e1: "iRule1=iInv2 "
     have "invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule1 iRule2)   invariants "
       by (metis  d e1)
            
   }
   moreover
   {assume e1: "iRule1\<noteq>iInv2 "
     have "invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule1 iRule2)   invariants "
       by (metis e e1)
            
   }
   ultimately show "invHoldForRule' s   (paraInv iInv1 iInv2) (paraRule iRule1 iRule2)   invariants "
     by blast
 qed
end


locale pRule2VspInv3=
  fixes paraRule ::"nat \<Rightarrow> nat\<Rightarrow>rule"  and paraInv::"nat \<Rightarrow> nat\<Rightarrow>nat\<Rightarrow>formula "  
  and iRule1::"nat"  and  iRule2::"nat"  and iInv1::"nat" and iInv2::"nat"  and iInv3::"nat" and N::"nat"
  and invariants::"formula set"
  assumes 
  b:"iRule1 = iInv1 \<longrightarrow> 
  invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule1 iRule2)  invariants "  and 
  c:" iRule1 = iInv2 \<longrightarrow> 
  invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule1 iRule2 ) invariants"  and
  d:"  iRule1 = iInv3 \<longrightarrow>
  invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule1 iRule2)  invariants" and
  
  e:" iRule1 \<noteq> iInv1 \<longrightarrow>iRule1 \<noteq> iInv2 \<longrightarrow> iRule1 \<noteq> iInv3 \<longrightarrow>
  invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule1 iRule2)  invariants"
begin
theorem  pRule1VspInv3:
  assumes a1:"iRule \<le> N"  and a2:" iInv1 \<le> N " and a3:"iInv2 \<le> N " and a4:"iInv3 \<le> N "
  and a5:"iInv1 \<noteq> iInv2"  and a6:"iInv1 \<noteq> iInv3"   and a7:"iInv2 \<noteq> iInv3"
  shows "invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule1 iRule2)  invariants " 
  proof -
   have d2:"iRule1=iInv1 \<or> iRule1=iInv2 \<or> iRule1=iInv3 \<or> ((iRule1 \<noteq> iInv1) \<and> (iRule1\<noteq>iInv2) \<and> iRule1 \<noteq> iInv3 )"  by auto
   moreover
   {assume e1:"iRule1=iInv1"
     have "invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule1 iRule2)  invariants  "
       by (cut_tac b e1, auto)
              
           
   }     
   moreover
   {assume e1:"iRule1 = iInv2"            
     have "invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule1 iRule2)  invariants  "
       by (cut_tac c e1,auto)
   }
   
       
   moreover
   {assume e1:"iRule1=iInv3"
     have "invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule1 iRule2)  invariants  " 
       by (cut_tac  d  e1,auto)
            
   }
   
   moreover
   {assume e1:"iRule1\<noteq>iInv1 \<and> iRule1\<noteq>iInv2 \<and> iRule1\<noteq>iInv3"
      have "invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule1 iRule2)  invariants  " 
       by (cut_tac  e  e1,auto)
            
   }
   ultimately show "invHoldForRule' s   (paraInv iInv1 iInv2 iInv3) (paraRule iRule1 iRule2)  invariants  " 
     by blast
 qed
end


locale iniImplyInv0= 
  fixes paraInv ::"  formula" and specOnAVar::"formula" and specOnAVars::"formula list"
  assumes a:" formEval  specOnAVar  s \<longrightarrow>formEval ( paraInv  ) s" and
  b:"specOnAVar \<in>set specOnAVars"
begin 
theorem iniImplyInv: 
  assumes a1:"ex0P N (  invariant = paraInv  )" and 
   a2:"formEval  (andList specOnAVars) s" 
  shows "formEval invariant  s " 
proof - 
  
 
  have b2:"formEval  specOnAVar  s"    
  by (metis a2 andList1 b)
 
  
 
  then show b5:"formEval (  invariant )   s" 
 
    apply -    
    apply(cut_tac a1 a2 a)
    by (metis (poly_guards_query) a ex0P_def)
   
   
qed 
end     
  
locale iniImplyInv1= 
  fixes paraInv ::" nat \<Rightarrow> formula"  and N::"nat" and specOnAVar::"formula" and specOnAVars::"formula list"
  assumes a:"\<forall>i . i\<le>N \<longrightarrow> formEval  specOnAVar  s \<longrightarrow>formEval ( paraInv i ) s" and
  b:"specOnAVar \<in>set specOnAVars"
begin 
theorem iniImplyInv: 
  assumes a1: " ex1P N (%i.  invariant = paraInv i )"   
  and a2:"formEval  (andList specOnAVars) s" 
  shows "formEval invariant  s " 
proof - 
  from a1 obtain i j where b1:"i \<le> N \<and> invariant =paraInv  i"  
    apply - 
    apply(simp add:ex1P_def) 
    apply auto 
    done 
 
  have b2:"formEval  specOnAVar  s"    
  by (metis a2 andList1 b)
 
  
 
  then have b5:"formEval ( paraInv i)   s" 
 
    apply -    
    apply(cut_tac a1 b2 a)
    by (metis b1 local.a)  
   
     
 then  show  "formEval invariant s "
 by (metis b1)    
   
qed 
end   
  
locale iniImplyInv2= 
  fixes paraInv ::" nat \<Rightarrow>nat \<Rightarrow> formula"  and N::"nat" and specOnAVar::"formula" and specOnAVars::"formula list"
  assumes a:"\<forall>i j. i\<le>N \<longrightarrow>  j\<le>N \<longrightarrow> formEval  specOnAVar  s \<longrightarrow>formEval ( paraInv i j) s" and
  b:"specOnAVar \<in>set specOnAVars"
begin 
theorem iniImplyInv: 
  assumes a1: " ex2P N (%i j.  invariant = paraInv i j)"   
  and a2:"formEval  (andList specOnAVars) s" 
  shows "formEval invariant  s " 
proof - 
  from a1 obtain i j where b1:"i \<le> N \<and> j\<le>N \<and> invariant =paraInv  i j"  
    apply - 
    apply(simp add:ex2P_def) 
    apply auto 
    done 
 
  have b2:"formEval  specOnAVar  s"    
  by (metis a2 andList1 b)
 
  
 
  then have b5:"formEval ( paraInv i j)   s" 
 
    apply -    
    apply(cut_tac a1 b2 a)
    by (metis b1 local.a)  
   
     
 then  show  "formEval invariant s "
 by (metis b1)    
   
qed 
end 


locale iniImplyInv3= 
  fixes paraInv ::" nat \<Rightarrow>nat \<Rightarrow> nat\<Rightarrow>formula"  and N::"nat" and specOnAVar::"formula" and specOnAVars::"formula list"
  assumes a:"\<forall>i j k. i\<le>N \<longrightarrow>  j\<le>N \<longrightarrow> k \<le>N \<longrightarrow> formEval  specOnAVar  s \<longrightarrow>formEval ( paraInv i j k) s" and
  b:"specOnAVar \<in>set specOnAVars"
begin 
theorem iniImplyInv: 
  assumes a1: " ex3P N (%i j k.  invariant = paraInv i j k)"   
  and a2:"formEval  (andList specOnAVars) s" 
  shows "formEval invariant  s " 
proof - 
  from a1 obtain i j k where b1:"i \<le> N \<and> j\<le>N \<and> k \<le>N \<and>  invariant =paraInv  i j k"  
    apply - 
    apply(simp add:ex3P_def) 
    apply auto 
    done 
 
  have b2:"formEval  specOnAVar  s"    
  by (metis a2 andList1 b)
 
  
 
  then have b5:"formEval ( paraInv i j k)   s" 
 
    apply -    
    apply(cut_tac a1 b2 a)
    by (metis b1 local.a)  
   
     
 then  show  "formEval invariant s "
 by (metis b1)    
   
qed 
end 

end
