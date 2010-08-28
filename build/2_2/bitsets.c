/* Generated by Nimrod Compiler v0.8.9 */
/*   (c) 2010 Andreas Rumpf */

typedef long long int NI;
typedef unsigned long long int NU;
#include "nimbase.h"

typedef struct TY99008 TY99008;
typedef struct TGenericSeq TGenericSeq;
typedef struct TNimType TNimType;
typedef struct TNimNode TNimNode;
struct TGenericSeq {
NI len;
NI space;
};
struct TNimType {
NI size;
NU8 kind;
NU8 flags;
TNimType* base;
TNimNode* node;
void* finalizer;
};
struct TNimNode {
NU8 kind;
NI offset;
TNimType* typ;
NCSTRING name;
NI len;
TNimNode** sons;
};
struct TY99008 {
  TGenericSeq Sup;
  NI8 data[SEQ_DECL_SIZE];
};
N_NIMCALL(void*, newSeq)(TNimType* Typ_12603, NI Len_12604);
N_NIMCALL(void, unsureAsgnRef)(void** Dest_11622, void* Src_11623);
extern TNimType* NTI99008; /* TBitSet */
N_NIMCALL(void, Bitsetinit_99010)(TY99008** B_99013, NI Length_99014) {
unsureAsgnRef((void**) &(*B_99013), (TY99008*) newSeq(NTI99008, Length_99014));
}
N_NIMCALL(void, Bitsetincl_99035)(TY99008** X_99038, NI64 Elem_99039) {
(*X_99038)->data[(NI64)(Elem_99039 / 8)] = (NI8)((*X_99038)->data[(NI64)(Elem_99039 / 8)] | ((NI8)(NU8)(NU)(((NI) ((NI64)((NU64)(1) << (NU64)((NI64)(Elem_99039 % 8))))))));
}
N_NIMCALL(void, Bitsetunion_99015)(TY99008** X_99018, TY99008* Y_99019) {
NI I_99120;
NI HEX3Atmp_99122;
NI Res_99124;
I_99120 = 0;
HEX3Atmp_99122 = 0;
HEX3Atmp_99122 = ((*X_99018)->Sup.len-1);
Res_99124 = 0;
Res_99124 = 0;
while (1) {
if (!(Res_99124 <= HEX3Atmp_99122)) goto LA1;
I_99120 = Res_99124;
(*X_99018)->data[I_99120] = (NI8)((*X_99018)->data[I_99120] | Y_99019->data[I_99120]);
Res_99124 += 1;
} LA1: ;
}
N_NIMCALL(void, Bitsetdiff_99020)(TY99008** X_99023, TY99008* Y_99024) {
NI I_99139;
NI HEX3Atmp_99141;
NI Res_99143;
I_99139 = 0;
HEX3Atmp_99141 = 0;
HEX3Atmp_99141 = ((*X_99023)->Sup.len-1);
Res_99143 = 0;
Res_99143 = 0;
while (1) {
if (!(Res_99143 <= HEX3Atmp_99141)) goto LA1;
I_99139 = Res_99143;
(*X_99023)->data[I_99139] = (NI8)((*X_99023)->data[I_99139] & (NI8)((NU8) ~(Y_99024->data[I_99139])));
Res_99143 += 1;
} LA1: ;
}
N_NIMCALL(void, Bitsetsymdiff_99025)(TY99008** X_99028, TY99008* Y_99029) {
NI I_99158;
NI HEX3Atmp_99160;
NI Res_99162;
I_99158 = 0;
HEX3Atmp_99160 = 0;
HEX3Atmp_99160 = ((*X_99028)->Sup.len-1);
Res_99162 = 0;
Res_99162 = 0;
while (1) {
if (!(Res_99162 <= HEX3Atmp_99160)) goto LA1;
I_99158 = Res_99162;
(*X_99028)->data[I_99158] = (NI8)((*X_99028)->data[I_99158] ^ Y_99029->data[I_99158]);
Res_99162 += 1;
} LA1: ;
}
N_NIMCALL(void, Bitsetintersect_99030)(TY99008** X_99033, TY99008* Y_99034) {
NI I_99177;
NI HEX3Atmp_99179;
NI Res_99181;
I_99177 = 0;
HEX3Atmp_99179 = 0;
HEX3Atmp_99179 = ((*X_99033)->Sup.len-1);
Res_99181 = 0;
Res_99181 = 0;
while (1) {
if (!(Res_99181 <= HEX3Atmp_99179)) goto LA1;
I_99177 = Res_99181;
(*X_99033)->data[I_99177] = (NI8)((*X_99033)->data[I_99177] & Y_99034->data[I_99177]);
Res_99181 += 1;
} LA1: ;
}
N_NIMCALL(NIM_BOOL, Bitsetin_99045)(TY99008* X_99047, NI64 E_99048) {
NIM_BOOL Result_99061;
Result_99061 = 0;
Result_99061 = !(((NI8)(X_99047->data[(NI64)(E_99048 / 8)] & ((NI8)(NU8)(NU)(((NI) ((NI64)((NU64)(1) << (NU64)((NI64)(E_99048 % 8)))))))) == ((NI8) 0)));
return Result_99061;
}
N_NIMCALL(NIM_BOOL, Bitsetcontains_99053)(TY99008* X_99055, TY99008* Y_99056) {
NIM_BOOL Result_99209;
NI I_99217;
NI HEX3Atmp_99221;
NI Res_99223;
Result_99209 = 0;
I_99217 = 0;
HEX3Atmp_99221 = 0;
HEX3Atmp_99221 = (X_99055->Sup.len-1);
Res_99223 = 0;
Res_99223 = 0;
while (1) {
if (!(Res_99223 <= HEX3Atmp_99221)) goto LA1;
I_99217 = Res_99223;
if (!!(((NI8)(X_99055->data[I_99217] & (NI8)((NU8) ~(Y_99056->data[I_99217]))) == ((NI8) 0)))) goto LA3;
Result_99209 = NIM_FALSE;
goto BeforeRet;
LA3: ;
Res_99223 += 1;
} LA1: ;
Result_99209 = NIM_TRUE;
BeforeRet: ;
return Result_99209;
}
N_NIMCALL(NIM_BOOL, Bitsetequals_99049)(TY99008* X_99051, TY99008* Y_99052) {
NIM_BOOL Result_99188;
NI I_99196;
NI HEX3Atmp_99200;
NI Res_99202;
Result_99188 = 0;
I_99196 = 0;
HEX3Atmp_99200 = 0;
HEX3Atmp_99200 = (X_99051->Sup.len-1);
Res_99202 = 0;
Res_99202 = 0;
while (1) {
if (!(Res_99202 <= HEX3Atmp_99200)) goto LA1;
I_99196 = Res_99202;
if (!!((X_99051->data[I_99196] == Y_99052->data[I_99196]))) goto LA3;
Result_99188 = NIM_FALSE;
goto BeforeRet;
LA3: ;
Res_99202 += 1;
} LA1: ;
Result_99188 = NIM_TRUE;
BeforeRet: ;
return Result_99188;
}
N_NOINLINE(void, bitsetsInit)(void) {
}
