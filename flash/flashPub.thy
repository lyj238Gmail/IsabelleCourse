theory flashPub imports cache localesDef
begin
section{*Main defintions*}
   
   consts M::nat

   definition Home::"nat"   where [simp]: "Home\<equiv>Suc M"

(***************definitions for the enumvalues types****************************************)
(***************definitions for the enumvalues types****************************************)
definition UNI_None::"nat"  where [simp]: "UNI_None\<equiv>  10"   

definition UNI_Get::"nat"  where [simp]: "UNI_Get\<equiv>  11"   

definition UNI_GetX::"nat"  where [simp]: "UNI_GetX\<equiv>  29"   

definition UNI_Put::"nat"  where [simp]: "UNI_Put\<equiv>  12"   

definition UNI_PutX::"nat"  where [simp]: "UNI_PutX\<equiv>  13"   

definition UNI_Nak::"nat"  where [simp]: "UNI_Nak\<equiv>  14"   

definition UNI_CMDType::"nat set" where [simp]: "UNI_CMDType \<equiv> {UNI_None,UNI_Get,UNI_GetX,UNI_Put,UNI_PutX,UNI_Nak}"

definition true::"nat"  where [simp]: "true\<equiv>  27"   

definition false::"nat"  where [simp]: "false\<equiv>  28"   

definition Bool::"nat set" where [simp]: "Bool \<equiv> {true,false}"

definition INV_None::"nat"  where [simp]: "INV_None\<equiv>  15"   

definition INV_Inv::"nat"  where [simp]: "INV_Inv\<equiv>  16"   

definition INV_InvAck::"nat"  where [simp]: "INV_InvAck\<equiv>  17"   

definition INV_CMDType::"nat set" where [simp]: "INV_CMDType \<equiv> {INV_None,INV_Inv,INV_InvAck}"

definition WB_None::"nat"  where [simp]: "WB_None\<equiv>  20"   

definition WB_Wb::"nat"  where [simp]: "WB_Wb\<equiv>  21"   

definition WB_CMDType::"nat set" where [simp]: "WB_CMDType \<equiv> {WB_None,WB_Wb}"

definition NAKC_None::"nat"  where [simp]: "NAKC_None\<equiv>  25"   

definition NAKC_Nakc::"nat"  where [simp]: "NAKC_Nakc\<equiv>  26"   

definition NAKC_CMDType::"nat set" where [simp]: "NAKC_CMDType \<equiv> {NAKC_None,NAKC_Nakc}"


definition RP_None::"nat"  where [simp]: "RP_None\<equiv>  18"   

definition RP_Replace::"nat"  where [simp]: "RP_Replace\<equiv>  19"   

definition RP_CMDType::"nat set" where [simp]: "RP_CMDType \<equiv> {RP_None,RP_Replace}"


definition NODE_None::"nat"  where [simp]: "NODE_None\<equiv>  7"   

definition NODE_Get::"nat"  where [simp]: "NODE_Get\<equiv>  8"   

definition NODE_GetX::"nat"  where [simp]: "NODE_GetX\<equiv>  9"   

definition NODE_CMDType::"nat set" where [simp]: "NODE_CMDType \<equiv> {NODE_None,NODE_Get,NODE_GetX}"

definition SHWB_None::"nat"  where [simp]: "SHWB_None\<equiv>  22"   

definition SHWB_ShWb::"nat"  where [simp]: "SHWB_ShWb\<equiv>  23"   

definition SHWB_FAck::"nat"  where [simp]: "SHWB_FAck\<equiv>  24"   

definition SHWB_CMDType::"nat set" where [simp]: "SHWB_CMDType \<equiv> {SHWB_None,SHWB_ShWb,SHWB_FAck}"

definition CACHE_I::"nat"  where [simp]: "CACHE_I\<equiv>  4"   

definition CACHE_S::"nat"  where [simp]: "CACHE_S\<equiv>  5"   

definition CACHE_E::"nat"  where [simp]: "CACHE_E\<equiv>  6"   

definition CACHE_STATEType::"nat set" where [simp]: "CACHE_STATEType \<equiv> {CACHE_I,CACHE_S,CACHE_E}"

(***************definitions for the axioms ****************************************)

axiomatization where axiomOn_CacheState  [simp]:"   s (IVar (Para ''CacheState'' i )) \<in> CACHE_STATEType "

axiomatization where axiomOn_Collecting  [simp]:"   s (IVar (Global ''Collecting'' )) \<in> Bool "


axiomatization where axiomOn_Dir_InvSet  [simp]:"   s (IVar (Para ''Dir_InvSet'' i )) \<in> Bool "

axiomatization where axiomOn_Dir_ShrSet  [simp]:"   s (IVar (Para ''Dir_ShrSet'' i )) \<in> Bool "

axiomatization where axiomOn_Dir_Dirty  [simp]:"   s (IVar (Global ''Dir_Dirty'' )) \<in> Bool "


axiomatization where axiomOn_Dir_HeadVld  [simp]:"   s (IVar (Global ''Dir_HeadVld'' )) \<in> Bool "

axiomatization where axiomOn_Dir_Pending  [simp]:"   s (IVar (Global ''Dir_Pending'' )) \<in> Bool "

axiomatization where axiomOn_Dir_ShrVld  [simp]:"   s (IVar (Global ''Dir_ShrVld'' )) \<in> Bool "

axiomatization where axiomOn_Dir_local  [simp]:"   s (IVar (Global ''Dir_local'' )) \<in> Bool "

axiomatization where axiomOn_FwdCmd  [simp]:"   s (IVar (Global ''FwdCmd'' )) \<in> UNI_CMDType "


axiomatization where axiomOn_InvMarked  [simp]:"   s (IVar (Para ''InvMarked'' i )) \<in> Bool "

axiomatization where axiomOn_InvMsg_Cmd  [simp]:"   s (IVar (Para ''InvMsg_Cmd'' i )) \<in> INV_CMDType "




axiomatization where axiomOn_LastWrVld  [simp]:"   s (IVar (Global ''LastWrVld'' )) \<in> Bool "


axiomatization where axiomOn_NakcMsg_Cmd  [simp]:"   s (IVar (Global ''NakcMsg_Cmd'' )) \<in> NAKC_CMDType "



axiomatization where axiomOn_RpMsg_Cmd  [simp]:"   s (IVar (Para ''RpMsg_Cmd'' i )) \<in> RP_CMDType "

axiomatization where axiomOn_ShWbMsg_Cmd  [simp]:"   s (IVar (Global ''ShWbMsg_Cmd'' )) \<in> SHWB_CMDType "



axiomatization where axiomOn_UniMsg_Cmd  [simp]:"   s (IVar (Para ''UniMsg_Cmd'' i )) \<in> UNI_CMDType "



axiomatization where axiomOn_WbMsg_Cmd  [simp]:"   s (IVar (Global ''WbMsg_Cmd'' )) \<in> WB_CMDType "



axiomatization where axiomOn_procCmd  [simp]:"   s (IVar (Para ''procCmd'' i )) \<in> NODE_CMDType "

definition NI_FAck::"   rule" where [simp]:
" NI_FAck    \<equiv>   
let g=( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_FAck ))  in 
let S=(
let S_1=( assign  (( Global ''ShWbMsg_Cmd''),  ( Const SHWB_None ) ) ) in
let S_2=( assign  (( Global ''Dir_Pending''),  ( Const false ) ) ) in
let S_3=( assign  (( Global ''Dir_HeadPtr''),  (iteForm ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))   ( IVar ( Global ''ShWbMsg_proc'') )  ( IVar ( Global ''Dir_HeadPtr'') )) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_Inv::" nat \<Rightarrow> rule" where [simp]:
" NI_Inv  iInv1 \<equiv>   
let g=( eqn ( IVar ( Para ''InvMsg_Cmd'' iInv1) )  ( Const INV_Inv ))  in 
let S=(
let S_1=( assign  (( Para ''InvMsg_Cmd'' iInv1),  ( Const INV_InvAck ) ) ) in
let S_2=( assign  (( Para ''CacheState'' iInv1),  ( Const CACHE_I ) ) ) in
let S_3=( assign  (( Para ''InvMarked'' iInv1),  (iteForm ( eqn ( IVar ( Para ''procCmd'' iInv1) )  ( Const NODE_Get ))   ( Const true )  ( IVar ( Para ''InvMarked'' iInv1) )) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_InvAck_1::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_InvAck_1  iInv1  iInv2 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm  (neg ( eqn  (Const iInv1)   (Const iInv2)) )    ( eqn ( IVar ( Para ''Dir_InvSet'' iInv2) )  ( Const true ))  )    ( eqn ( IVar ( Para ''Dir_InvSet'' iInv1) )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const true ))  )    ( eqn ( IVar ( Para ''InvMsg_Cmd'' iInv1) )  ( Const INV_InvAck ))  )  in 
let S=(
let S_1=( assign  (( Para ''InvMsg_Cmd'' iInv1),  ( Const INV_None ) ) ) in
let S_2=( assign  (( Para ''Dir_InvSet'' iInv1),  ( Const false ) ) ) in
parallelList [S_1,S_2]

) in 
guard g S"

definition NI_InvAck_1_Home::" nat \<Rightarrow> rule" where [simp]:
" NI_InvAck_1_Home  iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''InvMsg_Cmd'' iInv1) )  ( Const INV_InvAck ))    ( eqn ( IVar ( Para ''Dir_InvSet'' Home) )  ( Const true ))  )    ( eqn ( IVar ( Para ''Dir_InvSet'' iInv1) )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const true ))  )  in 
let S=(
let S_1=( assign  (( Para ''InvMsg_Cmd'' iInv1),  ( Const INV_None ) ) ) in
let S_2=( assign  (( Para ''Dir_InvSet'' iInv1),  ( Const false ) ) ) in
parallelList [S_1,S_2]

) in 
guard g S"

definition NI_InvAck_2::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_InvAck_2 N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm 
(    let natList=down N in 
    let paraForm=\<lambda>iInvForAll. ( andForm  (neg ( eqn (Const    iInvForAll )   (Const iInv1)) )    ( eqn ( IVar ( Para ''Dir_InvSet'' Home) )  ( Const false ))  )  in
       forallForm natList paraForm)
   ( eqn ( IVar ( Para ''Dir_InvSet'' iInv1) )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const true ))  )    ( eqn ( IVar ( Para ''InvMsg_Cmd'' iInv1) )  ( Const INV_InvAck ))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_Pending''),  ( Const false ) ) ) in
let S_2=( assign  (( Global ''Dir_local''),  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )   ( Const false )  ( IVar ( Global ''Dir_local'') )) ) ) in
parallelList [S_1,S_2]

) in 
guard g S"

definition NI_Local_GetX_GetX::" nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_GetX  iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))     (neg ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1)) )  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_2=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_GetX ) ) ) in
let S_3=( assign  (( Para ''UniMsg_proc'' iInv1),  ( IVar ( Global ''Dir_HeadPtr'') ) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_Local_GetX_Nak1::" nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_Nak1  iInv1 \<equiv>   
let g=( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const true ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Nak ) ) ) in
let S_2=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2]

) in 
guard g S"

definition NI_Local_GetX_Nak2::" nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_Nak2  iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))     (neg ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E )) )  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Nak ) ) ) in
let S_2=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2]

) in 
guard g S"

definition NI_Local_GetX_Nak3::" nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_Nak3  iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Nak ) ) ) in
let S_2=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2]

) in 
guard g S"

definition NI_Local_GetX_PutX1::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX1 N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_Get ))  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_local''),  ( Const false ) ) ) in
let S_2=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_3=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_4=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_5=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_6=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_8=( (let ps=% iInvForAll. let S_1=( assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) ) in
let S_2=( assign  (( Para ''Dir_InvSet'' iInvForAll),  ( Const false ) ) ) in
parallelList [S_1,S_2]

 in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_9=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_10=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
let S_11=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_I ) ) ) in
let S_12=( assign  (( Para ''InvMarked'' Home),  ( Const true ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10,S_11,S_12]

) in 
guard g S"

definition NI_Local_GetX_PutX2::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX2 N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))     (neg ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_Get )) )  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_local''),  ( Const false ) ) ) in
let S_2=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_3=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_4=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_5=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_6=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_8=( (let ps=% iInvForAll. let S_1=( assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) ) in
let S_2=( assign  (( Para ''Dir_InvSet'' iInvForAll),  ( Const false ) ) ) in
parallelList [S_1,S_2]

 in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_9=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_10=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
let S_11=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_I ) ) ) in
let S_12=( assign  (( Para ''InvMarked'' Home),  ( Const true ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10,S_11,S_12]

) in 
guard g S"

definition NI_Local_GetX_PutX3::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX3 N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_3=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_4=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_5=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_6=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_7=( (let ps=% iInvForAll. let S_1=( assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) ) in
let S_2=( assign  (( Para ''Dir_InvSet'' iInvForAll),  ( Const false ) ) ) in
parallelList [S_1,S_2]

 in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_8=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_9=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
let S_10=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_I ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10]

) in 
guard g S"

definition NI_Local_GetX_PutX4::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX4 N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    
(    let natList=down N in 
    let paraForm=\<lambda>iInvForAll. ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const false ))  in
       forallForm natList paraForm)
 )    ( eqn ( IVar ( Para ''Dir_ShrSet'' Home) )  ( Const false ))  )    ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_Get ))  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_local''),  ( Const false ) ) ) in
let S_2=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_3=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_4=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_5=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_6=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_8=( (let ps=% iInvForAll. let S_1=( assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) ) in
let S_2=( assign  (( Para ''Dir_InvSet'' iInvForAll),  ( Const false ) ) ) in
parallelList [S_1,S_2]

 in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_9=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_10=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
let S_11=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_I ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10,S_11]

) in 
guard g S"

definition NI_Local_GetX_PutX5::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX5 N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    
(    let natList=down N in 
    let paraForm=\<lambda>iInvForAll. ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const false ))  in
       forallForm natList paraForm)
 )    ( eqn ( IVar ( Para ''Dir_ShrSet'' Home) )  ( Const false ))  )     (neg ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_Get )) )  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_local''),  ( Const false ) ) ) in
let S_2=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_3=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_4=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_5=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_6=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_8=( (let ps=% iInvForAll. let S_1=( assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) ) in
let S_2=( assign  (( Para ''Dir_InvSet'' iInvForAll),  ( Const false ) ) ) in
parallelList [S_1,S_2]

 in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_9=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_10=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
let S_11=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_I ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10,S_11]

) in 
guard g S"

definition NI_Local_GetX_PutX6::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX6 N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    
(    let natList=down N in 
    let paraForm=\<lambda>iInvForAll. ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const false ))  in
       forallForm natList paraForm)
 )    ( eqn ( IVar ( Para ''Dir_ShrSet'' Home) )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_3=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_4=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_5=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_6=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_7=( (let ps=% iInvForAll. let S_1=( assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) ) in
let S_2=( assign  (( Para ''Dir_InvSet'' iInvForAll),  ( Const false ) ) ) in
parallelList [S_1,S_2]

 in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_8=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_9=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
let S_10=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_I ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10]

) in 
guard g S"

definition NI_Local_GetX_PutX7::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX7 N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))     (neg ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_Get )) )  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  )     (neg ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1)) )  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_local''),  ( Const false ) ) ) in
let S_3=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_4=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_5=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_6=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_8=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_9=( (let ps=% iInvForAll. assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_10=( (let ps=% iInvForAll. assign  (( Para ''Dir_InvSet'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const false )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )   ( Const true )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))  )   ( Const true )  ( Const false )))) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_11=( assign  (( Para ''InvMsg_Cmd'' Home),  ( Const INV_None ) ) ) in
let S_12=( (let ps=% iInvForAll. assign  (( Para ''InvMsg_Cmd'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const INV_None )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )   ( Const INV_Inv )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))  )   ( Const INV_Inv )  ( Const INV_None )))) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_13=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_14=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
let S_15=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_I ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10,S_11,S_12,S_13,S_14,S_15]

) in 
guard g S"

definition NI_Local_GetX_PutX8::" nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX8 N iInv1 iInv2\<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))     (neg ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_Get )) )  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  )    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInv2) )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))  )    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_local''),  ( Const false ) ) ) in
let S_3=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_4=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_5=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_6=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_8=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_9=( (let ps=% iInvForAll. assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_10=( (let ps=% iInvForAll. assign  (( Para ''Dir_InvSet'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const false )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )   ( Const true )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))  )   ( Const true )  ( Const false )))) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_11=( assign  (( Para ''InvMsg_Cmd'' Home),  ( Const INV_None ) ) ) in
let S_12=( (let ps=% iInvForAll. assign  (( Para ''InvMsg_Cmd'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const INV_None )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )   ( Const INV_Inv )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))  )   ( Const INV_Inv )  ( Const INV_None )))) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_13=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_14=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
let S_15=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_I ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10,S_11,S_12,S_13,S_14,S_15]

) in 
guard g S"

definition NI_Local_GetX_PutX8_home::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX8_home N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))     (neg ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_Get )) )  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  )    ( eqn ( IVar ( Para ''Dir_ShrSet'' Home) )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))  )    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_local''),  ( Const false ) ) ) in
let S_3=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_4=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_5=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_6=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_8=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_9=( (let ps=% iInvForAll. assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_10=( (let ps=% iInvForAll. assign  (( Para ''Dir_InvSet'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const false )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )   ( Const true )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))  )   ( Const true )  ( Const false )))) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_11=( assign  (( Para ''InvMsg_Cmd'' Home),  ( Const INV_None ) ) ) in
let S_12=( (let ps=% iInvForAll. assign  (( Para ''InvMsg_Cmd'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const INV_None )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )   ( Const INV_Inv )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))  )   ( Const INV_Inv )  ( Const INV_None )))) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_13=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_14=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
let S_15=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_I ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10,S_11,S_12,S_13,S_14,S_15]

) in 
guard g S"

definition NI_Local_GetX_PutX9::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX9 N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const false ))  )     (neg ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1)) )  )    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_local''),  ( Const false ) ) ) in
let S_3=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_4=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_5=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_6=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_8=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_9=( (let ps=% iInvForAll. assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_10=( (let ps=% iInvForAll. assign  (( Para ''Dir_InvSet'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const false )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )   ( Const true )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))  )   ( Const true )  ( Const false )))) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_11=( assign  (( Para ''InvMsg_Cmd'' Home),  ( Const INV_None ) ) ) in
let S_12=( (let ps=% iInvForAll. assign  (( Para ''InvMsg_Cmd'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const INV_None )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )   ( Const INV_Inv )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))  )   ( Const INV_Inv )  ( Const INV_None )))) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_13=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_14=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10,S_11,S_12,S_13,S_14]

) in 
guard g S"

definition NI_Local_GetX_PutX10::" nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX10 N iInv1 iInv2\<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInv2) )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))  )    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_local''),  ( Const false ) ) ) in
let S_3=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_4=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_5=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_6=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_8=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_9=( (let ps=% iInvForAll. assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_10=( (let ps=% iInvForAll. assign  (( Para ''Dir_InvSet'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const false )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )   ( Const true )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))  )   ( Const true )  ( Const false )))) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_11=( assign  (( Para ''InvMsg_Cmd'' Home),  ( Const INV_None ) ) ) in
let S_12=( (let ps=% iInvForAll. assign  (( Para ''InvMsg_Cmd'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const INV_None )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )   ( Const INV_Inv )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))  )   ( Const INV_Inv )  ( Const INV_None )))) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_13=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_14=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10,S_11,S_12,S_13,S_14]

) in 
guard g S"

definition NI_Local_GetX_PutX10_home::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX10_home N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''Dir_ShrSet'' Home) )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))  )    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_local''),  ( Const false ) ) ) in
let S_3=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_4=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_5=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_6=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_8=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_9=( (let ps=% iInvForAll. assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_10=( (let ps=% iInvForAll. assign  (( Para ''Dir_InvSet'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const false )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )   ( Const true )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))  )   ( Const true )  ( Const false )))) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_11=( assign  (( Para ''InvMsg_Cmd'' Home),  ( Const INV_None ) ) ) in
let S_12=( (let ps=% iInvForAll. assign  (( Para ''InvMsg_Cmd'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const INV_None )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )   ( Const INV_Inv )  (iteForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))  )   ( Const INV_Inv )  ( Const INV_None )))) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_13=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_14=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10,S_11,S_12,S_13,S_14]

) in 
guard g S"

definition NI_Local_GetX_PutX11::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_GetX_PutX11 N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_local''),  ( Const false ) ) ) in
let S_2=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_3=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_4=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_5=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_6=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
let S_8=( (let ps=% iInvForAll. assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_9=( (let ps=% iInvForAll. assign  (( Para ''Dir_InvSet'' iInvForAll),  ( Const false ) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_10=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_11=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
let S_12=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_I ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9,S_10,S_11,S_12]

) in 
guard g S"

definition NI_Local_Get_Get::" nat \<Rightarrow> rule" where [simp]:
" NI_Local_Get_Get  iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )     (neg ( eqn ( IVar ( Para ''RpMsg_Cmd'' iInv1) )  ( Const RP_Replace )) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_2=( assign  (( Para ''UniMsg_proc'' iInv1),  ( IVar ( Global ''Dir_HeadPtr'') ) ) ) in
parallelList [S_1,S_2]

) in 
guard g S"

definition NI_Local_Get_Nak1::" nat \<Rightarrow> rule" where [simp]:
" NI_Local_Get_Nak1  iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const true ))  )     (neg ( eqn ( IVar ( Para ''RpMsg_Cmd'' iInv1) )  ( Const RP_Replace )) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Nak ) ) ) in
let S_2=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2]

) in 
guard g S"

definition NI_Local_Get_Nak2::" nat \<Rightarrow> rule" where [simp]:
" NI_Local_Get_Nak2  iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))     (neg ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E )) )  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))  )     (neg ( eqn ( IVar ( Para ''RpMsg_Cmd'' iInv1) )  ( Const RP_Replace )) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Nak ) ) ) in
let S_2=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2]

) in 
guard g S"

definition NI_Local_Get_Nak3::" nat \<Rightarrow> rule" where [simp]:
" NI_Local_Get_Nak3  iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))  )     (neg ( eqn ( IVar ( Para ''RpMsg_Cmd'' iInv1) )  ( Const RP_Replace )) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Nak ) ) ) in
let S_2=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2]

) in 
guard g S"

definition NI_Local_Get_Put1::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Local_Get_Put1 N iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )     (neg ( eqn ( IVar ( Para ''RpMsg_Cmd'' iInv1) )  ( Const RP_Replace )) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_ShrVld''),  ( Const true ) ) ) in
let S_2=( assign  (( Para ''Dir_ShrSet'' iInv1),  ( Const true ) ) ) in
let S_3=( assign  (( Para ''Dir_InvSet'' Home),  ( IVar ( Para ''Dir_ShrSet'' Home) ) ) ) in
let S_4=( (let ps=% iInvForAll. assign  (( Para ''Dir_InvSet'' iInvForAll),  (iteForm ( eqn (Const    iInvForAll )   (Const iInv1))   ( Const true )  ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )) ) in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_5=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Put ) ) ) in
let S_6=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6]

) in 
guard g S"

definition NI_Local_Get_Put2::" nat \<Rightarrow> rule" where [simp]:
" NI_Local_Get_Put2  iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )     (neg ( eqn ( IVar ( Para ''RpMsg_Cmd'' iInv1) )  ( Const RP_Replace )) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_3=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Put ) ) ) in
let S_4=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2,S_3,S_4]

) in 
guard g S"

definition NI_Local_Get_Put3::" nat \<Rightarrow> rule" where [simp]:
" NI_Local_Get_Put3  iInv1 \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))  )    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )     (neg ( eqn ( IVar ( Para ''RpMsg_Cmd'' iInv1) )  ( Const RP_Replace )) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )  (Const    Home))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_Dirty''),  ( Const false ) ) ) in
let S_2=( assign  (( Global ''Dir_HeadVld''),  ( Const true ) ) ) in
let S_3=( assign  (( Global ''Dir_HeadPtr''),   (Const iInv1) ) ) in
let S_4=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_S ) ) ) in
let S_5=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Put ) ) ) in
let S_6=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6]

) in 
guard g S"

definition NI_Local_Put::"   rule" where [simp]:
" NI_Local_Put    \<equiv>   
let g=( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' Home),  ( Const UNI_None ) ) ) in
let S_2=( assign  (( Global ''Dir_Pending''),  ( Const false ) ) ) in
let S_3=( assign  (( Global ''Dir_Dirty''),  ( Const false ) ) ) in
let S_4=( assign  (( Global ''Dir_local''),  ( Const true ) ) ) in
let S_5=( assign  (( Para ''procCmd'' Home),  ( Const NODE_None ) ) ) in
let S_6=( assign  (( Para ''InvMarked'' Home),  (iteForm ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))   ( Const false )  ( IVar ( Para ''InvMarked'' Home) )) ) ) in
let S_7=( assign  (( Para ''CacheState'' Home),  (iteForm ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))   ( Const CACHE_I )  ( Const CACHE_S )) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7]

) in 
guard g S"

definition NI_Local_PutXAcksDone::"   rule" where [simp]:
" NI_Local_PutXAcksDone    \<equiv>   
let g=( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' Home),  ( Const UNI_None ) ) ) in
let S_2=( assign  (( Global ''Dir_Pending''),  ( Const false ) ) ) in
let S_3=( assign  (( Global ''Dir_local''),  ( Const true ) ) ) in
let S_4=( assign  (( Global ''Dir_HeadVld''),  ( Const false ) ) ) in
let S_5=( assign  (( Para ''procCmd'' Home),  ( Const NODE_None ) ) ) in
let S_6=( assign  (( Para ''InvMarked'' Home),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_E ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7]

) in 
guard g S"

definition NI_Nak::" nat \<Rightarrow> rule" where [simp]:
" NI_Nak  iInv1 \<equiv>   
let g=( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_None ))  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_None ) ) ) in
let S_2=( assign  (( Para ''procCmd'' iInv1),  ( Const NODE_None ) ) ) in
let S_3=( assign  (( Para ''InvMarked'' iInv1),  ( Const false ) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_Nak_Clear::"   rule" where [simp]:
" NI_Nak_Clear    \<equiv>   
let g=( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))  in 
let S=(
let S_1=( assign  (( Global ''NakcMsg_Cmd''),  ( Const NAKC_None ) ) ) in
let S_2=( assign  (( Global ''Dir_Pending''),  ( Const false ) ) ) in
parallelList [S_1,S_2]

) in 
guard g S"

definition NI_Nak_Home::"   rule" where [simp]:
" NI_Nak_Home    \<equiv>   
let g=( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_None ))  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' Home),  ( Const UNI_None ) ) ) in
let S_2=( assign  (( Para ''procCmd'' Home),  ( Const NODE_None ) ) ) in
let S_3=( assign  (( Para ''InvMarked'' Home),  ( Const false ) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_Remote_GetX_Nak::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Remote_GetX_Nak  iInv1  iInv2 \<equiv>   
let g=( andForm ( andForm ( andForm  (neg ( eqn  (Const iInv1)   (Const iInv2)) )     (neg ( eqn ( IVar ( Para ''CacheState'' iInv2) )  ( Const CACHE_E )) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))  )  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Nak ) ) ) in
let S_2=( assign  (( Para ''UniMsg_proc'' iInv1),   (Const iInv2) ) ) in
let S_3=( assign  (( Global ''NakcMsg_Cmd''),  ( Const NAKC_Nakc ) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_Remote_GetX_Nak_Home::" nat \<Rightarrow> rule" where [simp]:
" NI_Remote_GetX_Nak_Home  iInv1 \<equiv>   
let g=( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))     (neg ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E )) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' Home) )   (Const iInv1))  )  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' Home),  ( Const UNI_Nak ) ) ) in
let S_2=( assign  (( Para ''UniMsg_proc'' Home),   (Const iInv1) ) ) in
let S_3=( assign  (( Global ''NakcMsg_Cmd''),  ( Const NAKC_Nakc ) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_Remote_GetX_PutX::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Remote_GetX_PutX  iInv1  iInv2 \<equiv>   
let g=( andForm ( andForm ( andForm  (neg ( eqn  (Const iInv1)   (Const iInv2)) )    ( eqn ( IVar ( Para ''CacheState'' iInv2) )  ( Const CACHE_E ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))  )  in 
let S=(
let S_1=( assign  (( Para ''CacheState'' iInv2),  ( Const CACHE_I ) ) ) in
let S_2=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_PutX ) ) ) in
let S_3=( assign  (( Para ''UniMsg_proc'' iInv1),   (Const iInv2) ) ) in
let S_4=( assign  (( Global ''ShWbMsg_Cmd''),  ( Const SHWB_FAck ) ) ) in
let S_5=( assign  (( Global ''ShWbMsg_proc''),   (Const iInv1) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5]

) in 
guard g S"

definition NI_Remote_GetX_PutX_Home::" nat \<Rightarrow> rule" where [simp]:
" NI_Remote_GetX_PutX_Home  iInv1 \<equiv>   
let g=( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' Home) )   (Const iInv1))  )  in 
let S=(
let S_1=( assign  (( Para ''CacheState'' iInv1),  ( Const CACHE_I ) ) ) in
let S_2=( assign  (( Para ''UniMsg_Cmd'' Home),  ( Const UNI_PutX ) ) ) in
let S_3=( assign  (( Para ''UniMsg_proc'' Home),   (Const iInv1) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_Remote_Get_Nak1::" nat \<Rightarrow> rule" where [simp]:
" NI_Remote_Get_Nak1  iInv1 \<equiv>   
let g=( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))     (neg ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E )) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' Home) )   (Const iInv1))  )  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' Home),  ( Const UNI_Nak ) ) ) in
let S_2=( assign  (( Para ''UniMsg_proc'' Home),   (Const iInv1) ) ) in
let S_3=( assign  (( Global ''NakcMsg_Cmd''),  ( Const NAKC_Nakc ) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_Remote_Get_Nak2::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Remote_Get_Nak2  iInv1  iInv2 \<equiv>   
let g=( andForm ( andForm ( andForm  (neg ( eqn  (Const iInv1)   (Const iInv2)) )     (neg ( eqn ( IVar ( Para ''CacheState'' iInv2) )  ( Const CACHE_E )) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))  )  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Nak ) ) ) in
let S_2=( assign  (( Para ''UniMsg_proc'' iInv1),   (Const iInv2) ) ) in
let S_3=( assign  (( Global ''NakcMsg_Cmd''),  ( Const NAKC_Nakc ) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_Remote_Get_Put1::" nat \<Rightarrow> rule" where [simp]:
" NI_Remote_Get_Put1  iInv1 \<equiv>   
let g=( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' Home) )   (Const iInv1))  )  in 
let S=(
let S_1=( assign  (( Para ''CacheState'' iInv1),  ( Const CACHE_S ) ) ) in
let S_2=( assign  (( Para ''UniMsg_Cmd'' Home),  ( Const UNI_Put ) ) ) in
let S_3=( assign  (( Para ''UniMsg_proc'' Home),   (Const iInv1) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_Remote_Get_Put2::" nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
" NI_Remote_Get_Put2  iInv1  iInv2 \<equiv>   
let g=( andForm ( andForm ( andForm  (neg ( eqn  (Const iInv1)   (Const iInv2)) )    ( eqn ( IVar ( Para ''CacheState'' iInv2) )  ( Const CACHE_E ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))  )  in 
let S=(
let S_1=( assign  (( Para ''CacheState'' iInv2),  ( Const CACHE_S ) ) ) in
let S_2=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Put ) ) ) in
let S_3=( assign  (( Para ''UniMsg_proc'' iInv1),   (Const iInv2) ) ) in
let S_4=( assign  (( Global ''ShWbMsg_Cmd''),  ( Const SHWB_ShWb ) ) ) in
let S_5=( assign  (( Global ''ShWbMsg_proc''),   (Const iInv1) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5]

) in 
guard g S"

definition NI_Remote_Put::" nat \<Rightarrow> rule" where [simp]:
" NI_Remote_Put  iInv1 \<equiv>   
let g=( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Put ))  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_None ) ) ) in
let S_2=( assign  (( Para ''procCmd'' iInv1),  ( Const NODE_None ) ) ) in
let S_3=( assign  (( Para ''InvMarked'' iInv1),  (iteForm ( eqn ( IVar ( Para ''InvMarked'' iInv1) )  ( Const true ))   ( Const false )  ( IVar ( Para ''InvMarked'' iInv1) )) ) ) in
let S_4=( assign  (( Para ''CacheState'' iInv1),  (iteForm ( eqn ( IVar ( Para ''InvMarked'' iInv1) )  ( Const true ))   ( Const CACHE_I )  ( Const CACHE_S )) ) ) in
parallelList [S_1,S_2,S_3,S_4]

) in 
guard g S"

definition NI_Remote_PutX::" nat \<Rightarrow> rule" where [simp]:
" NI_Remote_PutX  iInv1 \<equiv>   
let g=( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Para ''procCmd'' iInv1) )  ( Const NODE_GetX ))  )  in 
let S=(
let S_1=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_None ) ) ) in
let S_2=( assign  (( Para ''procCmd'' iInv1),  ( Const NODE_None ) ) ) in
let S_3=( assign  (( Para ''InvMarked'' iInv1),  ( Const false ) ) ) in
let S_4=( assign  (( Para ''CacheState'' iInv1),  ( Const CACHE_E ) ) ) in
parallelList [S_1,S_2,S_3,S_4]

) in 
guard g S"

definition NI_Replace::" nat \<Rightarrow> rule" where [simp]:
" NI_Replace  iInv1 \<equiv>   
let g=( andForm ( eqn ( IVar ( Para ''RpMsg_Cmd'' iInv1) )  ( Const RP_Replace ))    ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const false ))  )  in 
let S=(
assign  (( Para ''RpMsg_Cmd'' iInv1),  ( Const RP_None ) )) in 
guard g S"

definition NI_ReplaceHome::"   rule" where [simp]:
" NI_ReplaceHome    \<equiv>   
let g=( andForm ( eqn ( IVar ( Para ''RpMsg_Cmd'' Home) )  ( Const RP_Replace ))    ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const false ))  )  in 
let S=(
assign  (( Para ''RpMsg_Cmd'' Home),  ( Const RP_None ) )) in 
guard g S"

definition NI_ReplaceHomeShrVld::"   rule" where [simp]:
" NI_ReplaceHomeShrVld    \<equiv>   
let g=( andForm ( eqn ( IVar ( Para ''RpMsg_Cmd'' Home) )  ( Const RP_Replace ))    ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))  )  in 
let S=(
let S_1=( assign  (( Para ''RpMsg_Cmd'' Home),  ( Const RP_None ) ) ) in
let S_2=( assign  (( Para ''Dir_ShrSet'' Home),  ( Const false ) ) ) in
let S_3=( assign  (( Para ''Dir_InvSet'' Home),  ( Const false ) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_ReplaceShrVld::" nat \<Rightarrow> rule" where [simp]:
" NI_ReplaceShrVld  iInv1 \<equiv>   
let g=( andForm ( eqn ( IVar ( Para ''RpMsg_Cmd'' iInv1) )  ( Const RP_Replace ))    ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))  )  in 
let S=(
let S_1=( assign  (( Para ''RpMsg_Cmd'' iInv1),  ( Const RP_None ) ) ) in
let S_2=( assign  (( Para ''Dir_ShrSet'' iInv1),  ( Const false ) ) ) in
let S_3=( assign  (( Para ''Dir_InvSet'' iInv1),  ( Const false ) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition NI_ShWb::" nat \<Rightarrow>   rule" where [simp]:
" NI_ShWb N  \<equiv>   
let g=( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  in 
let S=(
let S_1=( assign  (( Global ''ShWbMsg_Cmd''),  ( Const SHWB_None ) ) ) in
let S_2=( assign  (( Global ''Dir_Pending''),  ( Const false ) ) ) in
let S_3=( assign  (( Global ''Dir_Dirty''),  ( Const false ) ) ) in
let S_4=( assign  (( Global ''Dir_ShrVld''),  ( Const true ) ) ) in
let S_5=( (let ps=% iInvForAll. let S_1=( assign  (( Para ''Dir_ShrSet'' iInvForAll),  (iteForm ( eqn ( IVar ( Global ''ShWbMsg_proc'') )  (Const    iInvForAll ))   ( Const true )  (iteForm ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))   ( Const true )  ( Const false ))) ) ) in
let S_2=( assign  (( Para ''Dir_InvSet'' iInvForAll),  (iteForm ( eqn ( IVar ( Global ''ShWbMsg_proc'') )  (Const    iInvForAll ))   ( Const true )  (iteForm ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))   ( Const true )  ( Const false ))) ) ) in
parallelList [S_1,S_2]

 in
let natList=down N in
(forallSent natList  ps) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5]

) in 
guard g S"

definition NI_Wb::"   rule" where [simp]:
" NI_Wb    \<equiv>   
let g=( eqn ( IVar ( Global ''WbMsg_Cmd'') )  ( Const WB_Wb ))  in 
let S=(
let S_1=( assign  (( Global ''WbMsg_Cmd''),  ( Const WB_None ) ) ) in
let S_2=( assign  (( Global ''Dir_Dirty''),  ( Const false ) ) ) in
let S_3=( assign  (( Global ''Dir_HeadVld''),  ( Const false ) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition PI_Local_GetX_GetX1::"   rule" where [simp]:
" PI_Local_GetX_GetX1    \<equiv>   
let g=( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_I ))  )  in 
let S=(
let S_1=( assign  (( Para ''procCmd'' Home),  ( Const NODE_GetX ) ) ) in
let S_2=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_3=( assign  (( Para ''UniMsg_Cmd'' Home),  ( Const UNI_GetX ) ) ) in
let S_4=( assign  (( Para ''UniMsg_proc'' Home),  ( IVar ( Global ''Dir_HeadPtr'') ) ) ) in
parallelList [S_1,S_2,S_3,S_4]

) in 
guard g S"

definition PI_Local_GetX_GetX2::"   rule" where [simp]:
" PI_Local_GetX_GetX2    \<equiv>   
let g=( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  )  in 
let S=(
let S_1=( assign  (( Para ''procCmd'' Home),  ( Const NODE_GetX ) ) ) in
let S_2=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_3=( assign  (( Para ''UniMsg_Cmd'' Home),  ( Const UNI_GetX ) ) ) in
let S_4=( assign  (( Para ''UniMsg_proc'' Home),  ( IVar ( Global ''Dir_HeadPtr'') ) ) ) in
parallelList [S_1,S_2,S_3,S_4]

) in 
guard g S"

definition PI_Local_GetX_PutX1::" nat \<Rightarrow>   rule" where [simp]:
" PI_Local_GetX_PutX1 N  \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_I ))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_local''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_3=( (let ps=% iInvForAll. let S_1=( assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) ) in
let S_2=( assign  (( Para ''Dir_InvSet'' iInvForAll),  (iteForm ( orForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))    ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )  )   ( Const true )  ( Const false )) ) ) in
let S_3=( assign  (( Para ''InvMsg_Cmd'' iInvForAll),  (iteForm ( orForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))    ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )  )   ( Const INV_Inv )  ( Const INV_None )) ) ) in
parallelList [S_1,S_2,S_3]

 in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_4=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_5=( assign  (( Global ''Dir_HeadVld''),  ( Const false ) ) ) in
let S_6=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''procCmd'' Home),  ( Const NODE_None ) ) ) in
let S_8=( assign  (( Para ''InvMarked'' Home),  ( Const false ) ) ) in
let S_9=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_E ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8,S_9]

) in 
guard g S"

definition PI_Local_GetX_PutX2::" nat \<Rightarrow>   rule" where [simp]:
" PI_Local_GetX_PutX2 N  \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_local''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_3=( (let ps=% iInvForAll. let S_1=( assign  (( Para ''Dir_ShrSet'' iInvForAll),  ( Const false ) ) ) in
let S_2=( assign  (( Para ''Dir_InvSet'' iInvForAll),  (iteForm ( orForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))    ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )  )   ( Const true )  ( Const false )) ) ) in
let S_3=( assign  (( Para ''InvMsg_Cmd'' iInvForAll),  (iteForm ( orForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )  (Const    iInvForAll ))    ( andForm ( eqn ( IVar ( Global ''Dir_ShrVld'') )  ( Const true ))    ( eqn ( IVar ( Para ''Dir_ShrSet'' iInvForAll) )  ( Const true ))  )  )   ( Const INV_Inv )  ( Const INV_None )) ) ) in
parallelList [S_1,S_2,S_3]

 in
let natList=down N in
(forallSent natList  ps) ) ) in
let S_4=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_5=( assign  (( Global ''Dir_HeadVld''),  ( Const false ) ) ) in
let S_6=( assign  (( Global ''Dir_ShrVld''),  ( Const false ) ) ) in
let S_7=( assign  (( Para ''InvMarked'' Home),  ( Const false ) ) ) in
let S_8=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_E ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_8]

) in 
guard g S"

definition PI_Local_GetX_PutX3::"   rule" where [simp]:
" PI_Local_GetX_PutX3    \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_I ))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_local''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_3=( assign  (( Para ''procCmd'' Home),  ( Const NODE_None ) ) ) in
let S_4=( assign  (( Para ''InvMarked'' Home),  ( Const false ) ) ) in
let S_5=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_E ) ) ) in
let S_6=( assign  (( Para ''CacheData'' Home),  ( IVar ( Global ''MemData'') ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5,S_6]

) in 
guard g S"

definition PI_Local_GetX_PutX4::"   rule" where [simp]:
" PI_Local_GetX_PutX4    \<equiv>   
let g=( andForm ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))    ( eqn ( IVar ( Global ''Dir_HeadVld'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_local''),  ( Const true ) ) ) in
let S_2=( assign  (( Global ''Dir_Dirty''),  ( Const true ) ) ) in
let S_3=( assign  (( Para ''procCmd'' Home),  ( Const NODE_None ) ) ) in
let S_4=( assign  (( Para ''InvMarked'' Home),  ( Const false ) ) ) in
let S_5=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_E ) ) ) in
parallelList [S_1,S_2,S_3,S_4,S_5]

) in 
guard g S"

definition PI_Local_Get_Get::"   rule" where [simp]:
" PI_Local_Get_Get    \<equiv>   
let g=( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_I ))  )  in 
let S=(
let S_1=( assign  (( Para ''procCmd'' Home),  ( Const NODE_Get ) ) ) in
let S_2=( assign  (( Global ''Dir_Pending''),  ( Const true ) ) ) in
let S_3=( assign  (( Para ''UniMsg_Cmd'' Home),  ( Const UNI_Get ) ) ) in
let S_4=( assign  (( Para ''UniMsg_proc'' Home),  ( IVar ( Global ''Dir_HeadPtr'') ) ) ) in
parallelList [S_1,S_2,S_3,S_4]

) in 
guard g S"

definition PI_Local_Get_Put::"   rule" where [simp]:
" PI_Local_Get_Put    \<equiv>   
let g=( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_I ))  )  in 
let S=(
let S_1=( assign  (( Para ''procCmd'' Home),  ( Const NODE_None ) ) ) in
let S_2=( assign  (( Global ''Dir_local''),  ( Const true ) ) ) in
let S_3=( assign  (( Para ''InvMarked'' Home),  (iteForm ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))   ( Const false )  ( IVar ( Para ''InvMarked'' Home) )) ) ) in
let S_4=( assign  (( Para ''CacheState'' Home),  (iteForm ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))   ( Const CACHE_I )  ( Const CACHE_S )) ) ) in
parallelList [S_1,S_2,S_3,S_4]

) in 
guard g S"

definition PI_Local_PutX::"   rule" where [simp]:
" PI_Local_PutX    \<equiv>   
let g=( andForm ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))  )  in 
let S=(
let S_1=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_I ) ) ) in
let S_2=( assign  (( Global ''Dir_Dirty''),  ( Const false ) ) ) in
let S_3=( assign  (( Global ''Dir_local''),  (iteForm ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const true ))   ( IVar ( Global ''Dir_local'') )  ( Const false )) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition PI_Local_Replace::"   rule" where [simp]:
" PI_Local_Replace    \<equiv>   
let g=( andForm ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  )  in 
let S=(
let S_1=( assign  (( Global ''Dir_local''),  ( Const false ) ) ) in
let S_2=( assign  (( Para ''CacheState'' Home),  ( Const CACHE_I ) ) ) in
parallelList [S_1,S_2]

) in 
guard g S"

definition PI_Remote_Get::" nat \<Rightarrow> rule" where [simp]:
" PI_Remote_Get  iInv1 \<equiv>   
let g=( andForm ( eqn ( IVar ( Para ''procCmd'' iInv1) )  ( Const NODE_None ))    ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_I ))  )  in 
let S=(
let S_1=( assign  (( Para ''procCmd'' iInv1),  ( Const NODE_Get ) ) ) in
let S_2=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_Get ) ) ) in
let S_3=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition PI_Remote_GetX::" nat \<Rightarrow> rule" where [simp]:
" PI_Remote_GetX  iInv1 \<equiv>   
let g=( andForm ( eqn ( IVar ( Para ''procCmd'' iInv1) )  ( Const NODE_None ))    ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_I ))  )  in 
let S=(
let S_1=( assign  (( Para ''procCmd'' iInv1),  ( Const NODE_GetX ) ) ) in
let S_2=( assign  (( Para ''UniMsg_Cmd'' iInv1),  ( Const UNI_GetX ) ) ) in
let S_3=( assign  (( Para ''UniMsg_proc'' iInv1),  (Const    Home) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition PI_Remote_PutX::" nat \<Rightarrow> rule" where [simp]:
" PI_Remote_PutX  iInv1 \<equiv>   
let g=( andForm ( eqn ( IVar ( Para ''procCmd'' iInv1) )  ( Const NODE_None ))    ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))  )  in 
let S=(
let S_1=( assign  (( Para ''CacheState'' iInv1),  ( Const CACHE_I ) ) ) in
let S_2=( assign  (( Global ''WbMsg_Cmd''),  ( Const WB_Wb ) ) ) in
let S_3=( assign  (( Global ''WbMsg_proc''),   (Const iInv1) ) ) in
parallelList [S_1,S_2,S_3]

) in 
guard g S"

definition PI_Remote_Replace::" nat \<Rightarrow> rule" where [simp]:
" PI_Remote_Replace  iInv1 \<equiv>   
let g=( andForm ( eqn ( IVar ( Para ''procCmd'' iInv1) )  ( Const NODE_None ))    ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_S ))  )  in 
let S=(
( assign  (( Para ''RpMsg_Cmd'' iInv1),  ( Const RP_Replace ) ) )) in 
guard g S"

definition Store::" nat \<Rightarrow> rule" where [simp]:
" Store  iInv1 \<equiv>   
let g=( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))  in 
let S=(
assign  (( Para ''CacheData'' iInv1),  ( Const CACHE_E ) )) in 
guard g S"

definition StoreHome::"   rule" where [simp]:
" StoreHome    \<equiv>   
let g=( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))  in 
let S=(
assign  (( Para ''CacheData'' Home),  ( Const CACHE_E ) )) in 
guard g S"

definition rules::"nat \<Rightarrow> rule set"  where [simp] :
"rules N\<equiv> {r. ( r=NI_FAck )\<or>
ex1P N (%i.  r=NI_Inv i )  \<or>
ex2P N (%i j.  r=NI_InvAck_1 i j)  \<or>
ex1P N (%i.  r=NI_InvAck_1_Home i )  \<or>
ex1P N (%i.  r=NI_InvAck_2 N i)  \<or>
ex1P N (%i.  r=NI_Local_GetX_GetX i )  \<or>
ex1P N (%i.  r=NI_Local_GetX_Nak1 i )  \<or>
ex1P N (%i.  r=NI_Local_GetX_Nak2 i )  \<or>
ex1P N (%i.  r=NI_Local_GetX_Nak3 i )  \<or>
ex1P N (%i.  r=NI_Local_GetX_PutX1 N i)  \<or>
ex1P N (%i.  r=NI_Local_GetX_PutX2 N i)  \<or>
ex1P N (%i.  r=NI_Local_GetX_PutX3 N i)  \<or>
ex1P N (%i.  r=NI_Local_GetX_PutX4 N i)  \<or>
ex1P N (%i.  r=NI_Local_GetX_PutX5 N i)  \<or>
ex1P N (%i.  r=NI_Local_GetX_PutX6 N i)  \<or>
ex1P N (%i.  r=NI_Local_GetX_PutX7 N i)  \<or>
ex2P N (%i j.  r=NI_Local_GetX_PutX8 N i j)  \<or>
ex1P N (%i.  r=NI_Local_GetX_PutX8_home N i)  \<or>
ex1P N (%i.  r=NI_Local_GetX_PutX9 N i)  \<or>
ex2P N (%i j.  r=NI_Local_GetX_PutX10 N i j)  \<or>
ex1P N (%i.  r=NI_Local_GetX_PutX10_home N i)  \<or>
ex1P N (%i.  r=NI_Local_GetX_PutX11 N i)  \<or>
ex1P N (%i.  r=NI_Local_Get_Get i )  \<or>
ex1P N (%i.  r=NI_Local_Get_Nak1 i )  \<or>
ex1P N (%i.  r=NI_Local_Get_Nak2 i )  \<or>
ex1P N (%i.  r=NI_Local_Get_Nak3 i )  \<or>
ex1P N (%i.  r=NI_Local_Get_Put1 N i)  \<or>
ex1P N (%i.  r=NI_Local_Get_Put2 i )  \<or>
ex1P N (%i.  r=NI_Local_Get_Put3 i )  \<or>
( r=NI_Local_Put )\<or>
( r=NI_Local_PutXAcksDone )\<or>
ex1P N (%i.  r=NI_Nak i )  \<or>
( r=NI_Nak_Clear )\<or>
( r=NI_Nak_Home )\<or>
ex2P N (%i j.  r=NI_Remote_GetX_Nak i j)  \<or>
ex1P N (%i.  r=NI_Remote_GetX_Nak_Home i )  \<or>
ex2P N (%i j.  r=NI_Remote_GetX_PutX i j)  \<or>
ex1P N (%i.  r=NI_Remote_GetX_PutX_Home i )  \<or>
ex1P N (%i.  r=NI_Remote_Get_Nak1 i )  \<or>
ex2P N (%i j.  r=NI_Remote_Get_Nak2 i j)  \<or>
ex1P N (%i.  r=NI_Remote_Get_Put1 i )  \<or>
ex2P N (%i j.  r=NI_Remote_Get_Put2 i j)  \<or>
ex1P N (%i.  r=NI_Remote_Put i )  \<or>
ex1P N (%i.  r=NI_Remote_PutX i )  \<or>
ex1P N (%i.  r=NI_Replace i )  \<or>
( r=NI_ReplaceHome )\<or>
( r=NI_ReplaceHomeShrVld )\<or>
ex1P N (%i.  r=NI_ReplaceShrVld i )  \<or>
( r=NI_ShWb N)\<or>
( r=NI_Wb )\<or>
( r=PI_Local_GetX_GetX1 )\<or>
( r=PI_Local_GetX_GetX2 )\<or>
( r=PI_Local_GetX_PutX1 N)\<or>
( r=PI_Local_GetX_PutX2 N)\<or>
( r=PI_Local_GetX_PutX3 )\<or>
( r=PI_Local_GetX_PutX4 )\<or>
( r=PI_Local_Get_Get )\<or>
( r=PI_Local_Get_Put )\<or>
( r=PI_Local_PutX )\<or>
( r=PI_Local_Replace )\<or>
ex1P N (%i.  r=PI_Remote_Get i )  \<or>
ex1P N (%i.  r=PI_Remote_GetX i )  \<or>
ex1P N (%i.  r=PI_Remote_PutX i )  \<or>
ex1P N (%i.  r=PI_Remote_Replace i )  \<or>
ex1P N (%i.  r=Store i )  \<or>
( r=StoreHome )}"

definition inv1::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv1 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Para ''CacheState'' iInv2) )  ( Const CACHE_E ))  ) )   "
 definition inv2::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv2 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))     (neg ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2)) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv3::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv3 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))     (neg ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2)) )  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv4::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv4 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_PutX ))  ) )   "
 definition inv5::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv5 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_FAck ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv6::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv6 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv7::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv7 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_FAck ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv8::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv8 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv9::"nat \<Rightarrow> formula "  where [simp]:

       "inv9 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  ) )   "
 definition inv10::"nat \<Rightarrow> formula "  where [simp]:

       "inv10 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  ) )   "
 definition inv11::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv11 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_PutX ))  ) )   "
 definition inv12::" formula "  where [simp]:

       "inv12   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_FAck ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  ) )   "
 definition inv13::"nat \<Rightarrow> formula "  where [simp]:

       "inv13 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))  ) )   "
 definition inv14::"nat \<Rightarrow> formula "  where [simp]:

       "inv14 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))  ) )   "
 definition inv15::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv15 iInv1 iInv2  iInv3\<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''CacheState'' iInv3) )  ( Const CACHE_E ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv16::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv16 iInv1 iInv2  iInv3\<equiv> 
  
        (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv3) )   (Const iInv2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv3) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv17::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv17 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv18::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv18 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv19::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv19 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv20::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv20 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv21::"nat \<Rightarrow> formula "  where [simp]:

       "inv21 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))  ) )   "
 definition inv22::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv22 iInv1 iInv2  iInv3\<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''CacheState'' iInv3) )  ( Const CACHE_E ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv23::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv23 iInv1 iInv2  iInv3\<equiv> 
  
        (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv3) )   (Const iInv2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv3) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv24::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv24 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv25::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv25 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv26::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv26 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv27::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv27 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv28::"nat \<Rightarrow> formula "  where [simp]:

       "inv28 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))  ) )   "
 definition inv29::"nat \<Rightarrow> formula "  where [simp]:

       "inv29 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))  ) )   "
 definition inv30::"nat \<Rightarrow> formula "  where [simp]:

       "inv30 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  ) )   "
 definition inv31::"nat \<Rightarrow> formula "  where [simp]:

       "inv31 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Global ''WbMsg_Cmd'') )  ( Const WB_Wb ))  ) )   "
 definition inv32::"nat \<Rightarrow> formula "  where [simp]:

       "inv32 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))  ) )   "
 definition inv33::"nat \<Rightarrow> formula "  where [simp]:

       "inv33 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))  ) )   "
 definition inv34::"nat \<Rightarrow> formula "  where [simp]:

       "inv34 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))  ) )   "
 definition inv35::"nat \<Rightarrow> formula "  where [simp]:

       "inv35 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  ) )   "
 definition inv36::"nat \<Rightarrow> formula "  where [simp]:

       "inv36 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))  ) )   "
 definition inv37::" formula "  where [simp]:

       "inv37   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_FAck ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))  ) )   "
 definition inv38::" formula "  where [simp]:

       "inv38   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_FAck ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))  ) )   "
 definition inv39::" formula "  where [simp]:

       "inv39   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_FAck ))    ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))  ) )   "
 definition inv40::"nat \<Rightarrow> formula "  where [simp]:

       "inv40 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_I ))  ) )   "
 definition inv41::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv41 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''CacheState'' iInv2) )  ( Const CACHE_E ))  ) )   "
 definition inv42::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv42 iInv1 iInv2  iInv3\<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv3) )  ( Const UNI_PutX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv43::" formula "  where [simp]:

       "inv43   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  ) )   "
 definition inv44::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv44 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv45::" formula "  where [simp]:

       "inv45   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  ) )   "
 definition inv46::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv46 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv47::" formula "  where [simp]:

       "inv47   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  ) )   "
 definition inv48::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv48 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv2) )   (Const iInv1))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv49::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv49 iInv1 iInv2  iInv3\<equiv> 
  
        (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv2) )   (Const iInv3))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv50::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv50 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv2) )   (Const iInv1))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv51::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv51 iInv1 iInv2  iInv3\<equiv> 
  
        (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv2) )   (Const iInv3))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv52::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv52 iInv1 iInv2  iInv3\<equiv> 
  
        (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv3) )   (Const iInv1))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv3) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv53::" formula "  where [simp]:

       "inv53   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  ) )   "
 definition inv54::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv54 iInv1 iInv2  iInv3\<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv3) )  ( Const UNI_PutX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv55::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv55 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv56::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv56 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv57::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv57 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv2) )   (Const iInv1))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv58::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv58 iInv1 iInv2  iInv3\<equiv> 
  
        (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv2) )   (Const iInv3))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv59::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv59 iInv1 iInv2  iInv3\<equiv> 
  
        (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv3) )   (Const iInv2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv3) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv60::"nat \<Rightarrow> formula "  where [simp]:

       "inv60 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))  ) )   "
 definition inv61::"nat \<Rightarrow> formula "  where [simp]:

       "inv61 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  ) )   "
 definition inv62::"nat \<Rightarrow> formula "  where [simp]:

       "inv62 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Global ''WbMsg_Cmd'') )  ( Const WB_Wb ))  ) )   "
 definition inv63::"nat \<Rightarrow> formula "  where [simp]:

       "inv63 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))  ) )   "
 definition inv64::"nat \<Rightarrow> formula "  where [simp]:

       "inv64 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))  ) )   "
 definition inv65::"nat \<Rightarrow> formula "  where [simp]:

       "inv65 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  ) )   "
 definition inv66::" formula "  where [simp]:

       "inv66   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_FAck ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  ) )   "
 definition inv67::" formula "  where [simp]:

       "inv67   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_FAck ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))  ) )   "
 definition inv68::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv68 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Global ''ShWbMsg_proc'') )   (Const iInv1))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_FAck ))  )    ( eqn ( IVar ( Para ''CacheState'' iInv2) )  ( Const CACHE_E ))  ) )   "
 definition inv69::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv69 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))    ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))  )    ( eqn ( IVar ( Para ''CacheState'' iInv2) )  ( Const CACHE_E ))  ) )   "
 definition inv70::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv70 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_PutX ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  ) )   "
 definition inv71::" formula "  where [simp]:

       "inv71   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))    ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))  ) )   "
 definition inv72::" formula "  where [simp]:

       "inv72   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  ) )   "
 definition inv73::" formula "  where [simp]:

       "inv73   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  ) )   "
 definition inv74::" formula "  where [simp]:

       "inv74   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))  ) )   "
 definition inv75::" formula "  where [simp]:

       "inv75   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))  ) )   "
 definition inv76::" formula "  where [simp]:

       "inv76   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  ) )   "
 definition inv77::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv77 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv78::" formula "  where [simp]:

       "inv78   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  ) )   "
 definition inv79::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv79 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) )   "
 definition inv80::" formula "  where [simp]:

       "inv80   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''WbMsg_Cmd'') )  ( Const WB_Wb ))    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  ) )   "
 definition inv81::" formula "  where [simp]:

       "inv81   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''WbMsg_Cmd'') )  ( Const WB_Wb ))    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const true ))  ) )   "
 definition inv82::"nat \<Rightarrow> formula "  where [simp]:

       "inv82 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Para ''procCmd'' iInv1) )  ( Const NODE_None ))  ) )   "
 definition inv83::" formula "  where [simp]:

       "inv83   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  ) )   "
 definition inv84::" formula "  where [simp]:

       "inv84   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))    ( eqn ( IVar ( Global ''Dir_local'') )  ( Const false ))  ) )   "
 definition inv85::" formula "  where [simp]:

       "inv85   \<equiv> 
   
        (neg ( eqn ( IVar ( Para ''Dir_ShrSet'' Home) )  ( Const true )) )   "
 definition inv86::" formula "  where [simp]:

       "inv86   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_FAck ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  ) )   "
 definition inv87::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv87 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Global ''ShWbMsg_proc'') )   (Const iInv1))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_PutX ))  )    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_FAck ))  ) )   "
 definition inv88::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv88 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''CacheState'' iInv2) )  ( Const CACHE_E ))  ) )   "
 definition inv89::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv89 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''CacheState'' iInv2) )  ( Const CACHE_E ))  ) )   "
 definition inv90::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv90 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_PutX ))  )    ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))  ) )   "
 definition inv91::" formula "  where [simp]:

       "inv91   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  ) )   "
 definition inv92::" formula "  where [simp]:

       "inv92   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  ) )   "
 definition inv93::" formula "  where [simp]:

       "inv93   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))  ) )   "
 definition inv94::" formula "  where [simp]:

       "inv94   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  ) )   "
 definition inv95::" formula "  where [simp]:

       "inv95   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const true ))  ) )   "
 definition inv96::" formula "  where [simp]:

       "inv96   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''WbMsg_Cmd'') )  ( Const WB_Wb ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))  ) )   "
 definition inv97::" formula "  where [simp]:

       "inv97   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''WbMsg_Cmd'') )  ( Const WB_Wb ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  ) )   "
 definition inv98::" formula "  where [simp]:

       "inv98   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''WbMsg_Cmd'') )  ( Const WB_Wb ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))  ) )   "
 definition inv99::" formula "  where [simp]:

       "inv99   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''WbMsg_Cmd'') )  ( Const WB_Wb ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))  ) )   "
 definition inv100::" formula "  where [simp]:

       "inv100   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''WbMsg_Cmd'') )  ( Const WB_Wb ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  ) )   "
 definition inv101::"nat \<Rightarrow> formula "  where [simp]:

       "inv101 iInv1 \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''procCmd'' iInv1) )  ( Const NODE_None ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))  ) )   "
 definition inv102::" formula "  where [simp]:

       "inv102   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))  ) )   "
 definition inv103::" formula "  where [simp]:

       "inv103   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  ) )   "
 definition inv104::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv104 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_PutX ))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))  ) )   "
 definition inv105::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:

       "inv105 iInv1 iInv2 \<equiv> 
  
        (neg ( andForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv1))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_PutX ))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  ) )   "
 definition inv106::" formula "  where [simp]:

       "inv106   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  ) )   "
 definition inv107::" formula "  where [simp]:

       "inv107   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  ) )   "
 definition inv108::" formula "  where [simp]:

       "inv108   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))  ) )   "
 definition inv109::" formula "  where [simp]:

       "inv109   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))  ) )   "
 definition inv110::" formula "  where [simp]:

       "inv110   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  ) )   "
 definition inv111::" formula "  where [simp]:

       "inv111   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))  ) )   "
 definition inv112::" formula "  where [simp]:

       "inv112   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_I ))  ) )   "
 definition inv113::" formula "  where [simp]:

       "inv113   \<equiv> 
   
        (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''procCmd'' Home) )  ( Const NODE_None ))  ) )   "
 definition invariants::"nat \<Rightarrow> formula set"  where [simp] :
"invariants N\<equiv> {f. ex2P N (% i j.  f = inv1 i j)  \<or>
ex2P N (% i j.  f = inv2 i j)  \<or>
ex2P N (% i j.  f = inv3 i j)  \<or>
ex2P N (% i j.  f = inv4 i j)  \<or>
ex2P N (% i j.  f = inv5 i j)  \<or>
ex2P N (% i j.  f = inv6 i j)  \<or>
ex2P N (% i j.  f = inv7 i j)  \<or>
ex2P N (% i j.  f = inv8 i j)  \<or>
ex1P N (% i.  f= inv9 i)  \<or>
ex1P N (% i.  f= inv10 i)  \<or>
ex2P N (% i j.  f = inv11 i j)  \<or>
( f= inv12 )  \<or>
ex1P N (% i.  f= inv13 i)  \<or>
ex1P N (% i.  f= inv14 i)  \<or>
ex3P N (% i j k.  f= inv15 i j k)  \<or> 
ex3P N (% i j k.  f= inv16 i j k)  \<or> 
ex2P N (% i j.  f = inv17 i j)  \<or>
ex2P N (% i j.  f = inv18 i j)  \<or>
ex2P N (% i j.  f = inv19 i j)  \<or>
ex2P N (% i j.  f = inv20 i j)  \<or>
ex1P N (% i.  f= inv21 i)  \<or>
ex3P N (% i j k.  f= inv22 i j k)  \<or> 
ex3P N (% i j k.  f= inv23 i j k)  \<or> 
ex2P N (% i j.  f = inv24 i j)  \<or>
ex2P N (% i j.  f = inv25 i j)  \<or>
ex2P N (% i j.  f = inv26 i j)  \<or>
ex2P N (% i j.  f = inv27 i j)  \<or>
ex1P N (% i.  f= inv28 i)  \<or>
ex1P N (% i.  f= inv29 i)  \<or>
ex1P N (% i.  f= inv30 i)  \<or>
ex1P N (% i.  f= inv31 i)  \<or>
ex1P N (% i.  f= inv32 i)  \<or>
ex1P N (% i.  f= inv33 i)  \<or>
ex1P N (% i.  f= inv34 i)  \<or>
ex1P N (% i.  f= inv35 i)  \<or>
ex1P N (% i.  f= inv36 i)  \<or>
( f= inv37 )  \<or>
( f= inv38 )  \<or>
( f= inv39 )  \<or>
ex1P N (% i.  f= inv40 i)  \<or>
ex2P N (% i j.  f = inv41 i j)  \<or>
ex3P N (% i j k.  f= inv42 i j k)  \<or> 
( f= inv43 )  \<or>
ex2P N (% i j.  f = inv44 i j)  \<or>
( f= inv45 )  \<or>
ex2P N (% i j.  f = inv46 i j)  \<or>
( f= inv47 )  \<or>
ex2P N (% i j.  f = inv48 i j)  \<or>
ex3P N (% i j k.  f= inv49 i j k)  \<or> 
ex2P N (% i j.  f = inv50 i j)  \<or>
ex3P N (% i j k.  f= inv51 i j k)  \<or> 
ex3P N (% i j k.  f= inv52 i j k)  \<or> 
( f= inv53 )  \<or>
ex3P N (% i j k.  f= inv54 i j k)  \<or> 
ex2P N (% i j.  f = inv55 i j)  \<or>
ex2P N (% i j.  f = inv56 i j)  \<or>
ex2P N (% i j.  f = inv57 i j)  \<or>
ex3P N (% i j k.  f= inv58 i j k)  \<or> 
ex3P N (% i j k.  f= inv59 i j k)  \<or> 
ex1P N (% i.  f= inv60 i)  \<or>
ex1P N (% i.  f= inv61 i)  \<or>
ex1P N (% i.  f= inv62 i)  \<or>
ex1P N (% i.  f= inv63 i)  \<or>
ex1P N (% i.  f= inv64 i)  \<or>
ex1P N (% i.  f= inv65 i)  \<or>
( f= inv66 )  \<or>
( f= inv67 )  \<or>
ex2P N (% i j.  f = inv68 i j)  \<or>
ex2P N (% i j.  f = inv69 i j)  \<or>
ex2P N (% i j.  f = inv70 i j)  \<or>
( f= inv71 )  \<or>
( f= inv72 )  \<or>
( f= inv73 )  \<or>
( f= inv74 )  \<or>
( f= inv75 )  \<or>
( f= inv76 )  \<or>
ex2P N (% i j.  f = inv77 i j)  \<or>
( f= inv78 )  \<or>
ex2P N (% i j.  f = inv79 i j)  \<or>
( f= inv80 )  \<or>
( f= inv81 )  \<or>
ex1P N (% i.  f= inv82 i)  \<or>
( f= inv83 )  \<or>
( f= inv84 )  \<or>
( f= inv85 )  \<or>
( f= inv86 )  \<or>
ex2P N (% i j.  f = inv87 i j)  \<or>
ex2P N (% i j.  f = inv88 i j)  \<or>
ex2P N (% i j.  f = inv89 i j)  \<or>
ex2P N (% i j.  f = inv90 i j)  \<or>
( f= inv91 )  \<or>
( f= inv92 )  \<or>
( f= inv93 )  \<or>
( f= inv94 )  \<or>
( f= inv95 )  \<or>
( f= inv96 )  \<or>
( f= inv97 )  \<or>
( f= inv98 )  \<or>
( f= inv99 )  \<or>
( f= inv100 )  \<or>
ex1P N (% i.  f= inv101 i)  \<or>
( f= inv102 )  \<or>
( f= inv103 )  \<or>
ex2P N (% i j.  f = inv104 i j)  \<or>
ex2P N (% i j.  f = inv105 i j)  \<or>
( f= inv106 )  \<or>
( f= inv107 )  \<or>
( f= inv108 )  \<or>
( f= inv109 )  \<or>
( f= inv110 )  \<or>
( f= inv111 )  \<or>
( f= inv112 )  \<or>
( f= inv113 )   }"

 definition iniStateSpecOfDir_ShrSet_i::" nat \<Rightarrow>  formula" where [simp] :

  " iniStateSpecOfDir_ShrSet_i N\<equiv>  forallForm  (down N)  (%iInv1. eqn ( IVar ( Para ''Dir_ShrSet'' iInv1) ) ( Const false ))"


 definition iniStateSpecOfDir_ShrSet::"   formula" where [simp] :

  " iniStateSpecOfDir_ShrSet \<equiv>  eqn ( ( IVar ( Para ''Dir_ShrSet'' Home) )) ( Const false )"


 definition iniStateSpecOfDir_Pending::"   formula" where [simp] :

  " iniStateSpecOfDir_Pending \<equiv>  eqn ( ( IVar ( Global ''Dir_Pending'') )) ( Const false )"


 definition iniStateSpecOfCacheState_i::" nat \<Rightarrow>  formula" where [simp] :

  " iniStateSpecOfCacheState_i N\<equiv>  forallForm  (down N)  (%iInv1. eqn ( IVar ( Para ''CacheState'' iInv1) ) ( Const CACHE_I ))"


 definition iniStateSpecOfCacheState::"   formula" where [simp] :

  " iniStateSpecOfCacheState \<equiv>  eqn ( ( IVar ( Para ''CacheState'' Home) )) ( Const CACHE_I )"


 definition iniStateSpecOfInvMsg_Cmd_i::" nat \<Rightarrow>  formula" where [simp] :

  " iniStateSpecOfInvMsg_Cmd_i N\<equiv>  forallForm  (down N)  (%iInv1. eqn ( IVar ( Para ''InvMsg_Cmd'' iInv1) ) ( Const INV_None ))"


 definition iniStateSpecOfInvMsg_Cmd::"   formula" where [simp] :

  " iniStateSpecOfInvMsg_Cmd \<equiv>  eqn ( ( IVar ( Para ''InvMsg_Cmd'' Home) )) ( Const INV_None )"


 definition iniStateSpecOfShWbMsg_Cmd::"   formula" where [simp] :

  " iniStateSpecOfShWbMsg_Cmd \<equiv>  eqn ( ( IVar ( Global ''ShWbMsg_Cmd'') )) ( Const SHWB_None )"


 definition iniStateSpecOfUniMsg_Cmd_i::" nat \<Rightarrow>  formula" where [simp] :

  " iniStateSpecOfUniMsg_Cmd_i N\<equiv>  forallForm  (down N)  (%iInv1. eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) ) ( Const UNI_None ))"


 definition iniStateSpecOfUniMsg_Cmd::"   formula" where [simp] :

  " iniStateSpecOfUniMsg_Cmd \<equiv>  eqn ( ( IVar ( Para ''UniMsg_Cmd'' Home) )) ( Const UNI_None )"


 definition iniStateSpecOfprocCmd_i::" nat \<Rightarrow>  formula" where [simp] :

  " iniStateSpecOfprocCmd_i N\<equiv>  forallForm  (down N)  (%iInv1. eqn ( IVar ( Para ''procCmd'' iInv1) ) ( Const NODE_None ))"


 definition iniStateSpecOfprocCmd::"   formula" where [simp] :

  " iniStateSpecOfprocCmd \<equiv>  eqn ( ( IVar ( Para ''procCmd'' Home) )) ( Const NODE_None )"


 definition iniStateSpecOfInvMarked_i::" nat \<Rightarrow>  formula" where [simp] :

  " iniStateSpecOfInvMarked_i N\<equiv>  forallForm  (down N)  (%iInv1. eqn ( IVar ( Para ''InvMarked'' iInv1) ) ( Const false ))"


 definition iniStateSpecOfInvMarked::"   formula" where [simp] :

  " iniStateSpecOfInvMarked \<equiv>  eqn ( ( IVar ( Para ''InvMarked'' Home) )) ( Const false )"


 definition iniStateSpecOfDir_ShrVld::"   formula" where [simp] :

  " iniStateSpecOfDir_ShrVld \<equiv>  eqn ( ( IVar ( Global ''Dir_ShrVld'') )) ( Const false )"


 definition iniStateSpecOfWbMsg_Cmd::"   formula" where [simp] :

  " iniStateSpecOfWbMsg_Cmd \<equiv>  eqn ( ( IVar ( Global ''WbMsg_Cmd'') )) ( Const WB_None )"


 definition iniStateSpecOfDir_InvSet_i::" nat \<Rightarrow>  formula" where [simp] :

  " iniStateSpecOfDir_InvSet_i N\<equiv>  forallForm  (down N)  (%iInv1. eqn ( IVar ( Para ''Dir_InvSet'' iInv1) ) ( Const CACHE_I ))"


 definition iniStateSpecOfDir_InvSet::"   formula" where [simp] :

  " iniStateSpecOfDir_InvSet \<equiv>  eqn ( ( IVar ( Para ''Dir_InvSet'' Home) )) ( Const false )"


 definition iniStateSpecOfDir_HeadVld::"   formula" where [simp] :

  " iniStateSpecOfDir_HeadVld \<equiv>  eqn ( ( IVar ( Global ''Dir_HeadVld'') )) ( Const false )"


 definition iniStateSpecOfRpMsg_Cmd_i::" nat \<Rightarrow>  formula" where [simp] :

  " iniStateSpecOfRpMsg_Cmd_i N\<equiv>  forallForm  (down N)  (%iInv1. eqn ( IVar ( Para ''RpMsg_Cmd'' iInv1) ) ( Const RP_None ))"


 definition iniStateSpecOfRpMsg_Cmd::"   formula" where [simp] :

  " iniStateSpecOfRpMsg_Cmd \<equiv>  eqn ( ( IVar ( Para ''RpMsg_Cmd'' Home) )) ( Const RP_None )"


 definition iniStateSpecOfDir_Dirty::"   formula" where [simp] :

  " iniStateSpecOfDir_Dirty \<equiv>  eqn ( ( IVar ( Global ''Dir_Dirty'') )) ( Const false )"


 definition iniStateSpecOfNakcMsg_Cmd::"   formula" where [simp] :

  " iniStateSpecOfNakcMsg_Cmd \<equiv>  eqn ( ( IVar ( Global ''NakcMsg_Cmd'') )) ( Const NAKC_None )"


 definition iniStateSpecOfDir_local::"   formula" where [simp] :

  " iniStateSpecOfDir_local \<equiv>  eqn ( ( IVar ( Global ''Dir_local'') )) ( Const false )"


definition allIniSpecs ::"nat\<Rightarrow>formula list" where [simp]:

   "allIniSpecs  N \<equiv>[ (  iniStateSpecOfDir_ShrSet )
, (  iniStateSpecOfDir_Pending )
, (  iniStateSpecOfCacheState_i N )
, (  iniStateSpecOfCacheState )
, (  iniStateSpecOfInvMsg_Cmd_i N )
, (  iniStateSpecOfInvMsg_Cmd )
, (  iniStateSpecOfShWbMsg_Cmd )
, (  iniStateSpecOfUniMsg_Cmd_i N )
, (  iniStateSpecOfUniMsg_Cmd )
, (  iniStateSpecOfprocCmd_i N )
, (  iniStateSpecOfprocCmd )
, (  iniStateSpecOfInvMarked_i N )
, (  iniStateSpecOfInvMarked )
, (  iniStateSpecOfDir_ShrVld )
, (  iniStateSpecOfWbMsg_Cmd )
, (  iniStateSpecOfDir_InvSet_i N )
, (  iniStateSpecOfDir_InvSet )
, (  iniStateSpecOfDir_HeadVld )
, (  iniStateSpecOfRpMsg_Cmd_i N )
, (  iniStateSpecOfRpMsg_Cmd )
, (  iniStateSpecOfDir_Dirty )
, (  iniStateSpecOfNakcMsg_Cmd )
, (  iniStateSpecOfDir_local )
, (  iniStateSpecOfDir_ShrSet_i N )
]"

interpretation iniImply_inv1:iniImplyInv2 "inv1::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv2:iniImplyInv2 "inv2::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv3:iniImplyInv2 "inv3::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv4:iniImplyInv2 "inv4::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv5:iniImplyInv2 "inv5::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv6:iniImplyInv2 "inv6::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv7:iniImplyInv2 "inv7::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv8:iniImplyInv2 "inv8::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv9:iniImplyInv1 "inv9::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv10:iniImplyInv1 "inv10::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv11:iniImplyInv2 "inv11::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv12:iniImplyInv0 "inv12:: formula"  "iniStateSpecOfShWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv13:iniImplyInv1 "inv13::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv14:iniImplyInv1 "inv14::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv15:iniImplyInv3 "inv15::nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv3_def,  auto ) done

interpretation iniImply_inv16:iniImplyInv3 "inv16::nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv3_def,  auto ) done

interpretation iniImply_inv17:iniImplyInv2 "inv17::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv18:iniImplyInv2 "inv18::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv19:iniImplyInv2 "inv19::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv20:iniImplyInv2 "inv20::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv21:iniImplyInv1 "inv21::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv22:iniImplyInv3 "inv22::nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv3_def,  auto ) done

interpretation iniImply_inv23:iniImplyInv3 "inv23::nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv3_def,  auto ) done

interpretation iniImply_inv24:iniImplyInv2 "inv24::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv25:iniImplyInv2 "inv25::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv26:iniImplyInv2 "inv26::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv27:iniImplyInv2 "inv27::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv28:iniImplyInv1 "inv28::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv29:iniImplyInv1 "inv29::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv30:iniImplyInv1 "inv30::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv31:iniImplyInv1 "inv31::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv32:iniImplyInv1 "inv32::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv33:iniImplyInv1 "inv33::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv34:iniImplyInv1 "inv34::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfDir_local ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv35:iniImplyInv1 "inv35::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv36:iniImplyInv1 "inv36::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv37:iniImplyInv0 "inv37:: formula"  "iniStateSpecOfShWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv38:iniImplyInv0 "inv38:: formula"  "iniStateSpecOfShWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv39:iniImplyInv0 "inv39:: formula"  "iniStateSpecOfShWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv40:iniImplyInv1 "inv40::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv41:iniImplyInv2 "inv41::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv42:iniImplyInv3 "inv42::nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv3_def,  auto ) done

interpretation iniImply_inv43:iniImplyInv0 "inv43:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv44:iniImplyInv2 "inv44::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv45:iniImplyInv0 "inv45:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv46:iniImplyInv2 "inv46::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv47:iniImplyInv0 "inv47:: formula"  "iniStateSpecOfNakcMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv48:iniImplyInv2 "inv48::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv49:iniImplyInv3 "inv49::nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv3_def,  auto ) done

interpretation iniImply_inv50:iniImplyInv2 "inv50::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv51:iniImplyInv3 "inv51::nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv3_def,  auto ) done

interpretation iniImply_inv52:iniImplyInv3 "inv52::nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv3_def,  auto ) done

interpretation iniImply_inv53:iniImplyInv0 "inv53:: formula"  "iniStateSpecOfShWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv54:iniImplyInv3 "inv54::nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv3_def,  auto ) done

interpretation iniImply_inv55:iniImplyInv2 "inv55::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv56:iniImplyInv2 "inv56::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv57:iniImplyInv2 "inv57::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv58:iniImplyInv3 "inv58::nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv3_def,  auto ) done

interpretation iniImply_inv59:iniImplyInv3 "inv59::nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv3_def,  auto ) done

interpretation iniImply_inv60:iniImplyInv1 "inv60::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv61:iniImplyInv1 "inv61::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv62:iniImplyInv1 "inv62::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv63:iniImplyInv1 "inv63::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv64:iniImplyInv1 "inv64::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv65:iniImplyInv1 "inv65::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv66:iniImplyInv0 "inv66:: formula"  "iniStateSpecOfShWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv67:iniImplyInv0 "inv67:: formula"  "iniStateSpecOfShWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv68:iniImplyInv2 "inv68::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv69:iniImplyInv2 "inv69::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv70:iniImplyInv2 "inv70::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv71:iniImplyInv0 "inv71:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv72:iniImplyInv0 "inv72:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv73:iniImplyInv0 "inv73:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv74:iniImplyInv0 "inv74:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv75:iniImplyInv0 "inv75:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv76:iniImplyInv0 "inv76:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv77:iniImplyInv2 "inv77::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv78:iniImplyInv0 "inv78:: formula"  "iniStateSpecOfNakcMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv79:iniImplyInv2 "inv79::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv80:iniImplyInv0 "inv80:: formula"  "iniStateSpecOfWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv81:iniImplyInv0 "inv81:: formula"  "iniStateSpecOfWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv82:iniImplyInv1 "inv82::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv83:iniImplyInv0 "inv83:: formula"  "iniStateSpecOfCacheState ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv84:iniImplyInv0 "inv84:: formula"  "iniStateSpecOfCacheState ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv85:iniImplyInv0 "inv85:: formula"  "iniStateSpecOfDir_ShrSet ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv86:iniImplyInv0 "inv86:: formula"  "iniStateSpecOfShWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv87:iniImplyInv2 "inv87::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfShWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv88:iniImplyInv2 "inv88::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv89:iniImplyInv2 "inv89::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfCacheState_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv90:iniImplyInv2 "inv90::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfNakcMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv91:iniImplyInv0 "inv91:: formula"  "iniStateSpecOfNakcMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv92:iniImplyInv0 "inv92:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv93:iniImplyInv0 "inv93:: formula"  "iniStateSpecOfNakcMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv94:iniImplyInv0 "inv94:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv95:iniImplyInv0 "inv95:: formula"  "iniStateSpecOfCacheState ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv96:iniImplyInv0 "inv96:: formula"  "iniStateSpecOfWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv97:iniImplyInv0 "inv97:: formula"  "iniStateSpecOfWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv98:iniImplyInv0 "inv98:: formula"  "iniStateSpecOfWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv99:iniImplyInv0 "inv99:: formula"  "iniStateSpecOfWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv100:iniImplyInv0 "inv100:: formula"  "iniStateSpecOfWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv101:iniImplyInv1 "inv101::nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd_i N::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv1_def,  auto ) done

interpretation iniImply_inv102:iniImplyInv0 "inv102:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv103:iniImplyInv0 "inv103:: formula"  "iniStateSpecOfCacheState ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv104:iniImplyInv2 "inv104::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv105:iniImplyInv2 "inv105::nat\<Rightarrow>nat\<Rightarrow>formula" "N::nat" "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv2_def,  auto ) done

interpretation iniImply_inv106:iniImplyInv0 "inv106:: formula"  "iniStateSpecOfNakcMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv107:iniImplyInv0 "inv107:: formula"  "iniStateSpecOfShWbMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv108:iniImplyInv0 "inv108:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv109:iniImplyInv0 "inv109:: formula"  "iniStateSpecOfCacheState ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv110:iniImplyInv0 "inv110:: formula"  "iniStateSpecOfCacheState ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv111:iniImplyInv0 "inv111:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv112:iniImplyInv0 "inv112:: formula"  "iniStateSpecOfCacheState ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

interpretation iniImply_inv113:iniImplyInv0 "inv113:: formula"  "iniStateSpecOfUniMsg_Cmd ::formula" "allIniSpecs N" 

     apply(unfold iniImplyInv0_def,  auto ) done

abbreviation N::"nat"   where   "N\<equiv> M"

end
