/*
The MIT License

Copyright (c) 2007 Adam Kiezun

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*/
#include <jni.h>
#include <stdio.h>
#include <stdlib.h>
#include "STPJNI.h"
#include "c_interface.h"

JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1setFlags (JNIEnv *env, jclass clazz, jchar o)
{
  vc_setFlags(o);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1createValidityChecker (JNIEnv *env, jclass clazz)
{
  return (jlong)vc_createValidityChecker();
}
 
JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1boolType (JNIEnv *env, jclass clazz, jlong vc)
{
  return (jlong)vc_boolType((VC)vc);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1arrayType (JNIEnv *env, jclass clazz, jlong vc, jlong typeIndex, jlong typeData)
{
 return (jlong)vc_arrayType((VC)vc, (Type)typeIndex, (Type)typeData);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1varExpr (JNIEnv *env, jclass clazz, jlong vc, jstring name, jlong type)
{
  jboolean iscopy;
  const char *namestr = env->GetStringUTFChars(name, &iscopy);
  jlong result = (jlong)vc_varExpr((VC)vc, const_cast<char*>(namestr), (Type)type);
  env->ReleaseStringUTFChars(name, namestr);
  return result;
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1varExpr1 (JNIEnv *env, jclass clazz, jlong vc, jstring name, jint indexwidth, jint valuewidth)
{
  jboolean iscopy;
  const char *namestr = env->GetStringUTFChars(name, &iscopy);
  jlong result = (jlong)vc_varExpr1((VC)vc, const_cast<char*>(namestr), (int)indexwidth, (int)valuewidth);
  env->ReleaseStringUTFChars(name, namestr);
  return result;
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1getType (JNIEnv *env, jclass clazz, jlong vc, jlong e)
{
  return (jlong)vc_getType((VC)vc, (Expr)e);
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_vc_1getBVLength (JNIEnv *env, jclass clazz, jlong vc, jlong e)
{
  return (jint)vc_getBVLength((VC)vc, (Expr)e);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1eqExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_eqExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1trueExpr (JNIEnv *env, jclass clazz, jlong vc)
{
  return (jlong)vc_trueExpr((VC)vc);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1falseExpr (JNIEnv *env, jclass clazz, jlong vc)
{
  return (jlong)vc_falseExpr((VC)vc);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1notExpr (JNIEnv *env, jclass clazz, jlong vc, jlong expr)
{
  return (jlong)vc_notExpr((VC)vc, (Expr)expr);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1andExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_andExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1andExprN (JNIEnv *env, jclass clazz, jlong vc, jlongArray children, jint numOfChildNodes)
{
  jlong *body = env->GetLongArrayElements(children, 0);
  Expr* arr = (Expr*)malloc(sizeof(Expr)*(int)numOfChildNodes);  
  for (int i = 0; i < numOfChildNodes; i++){
    arr[i]= (Expr)body[i];
  }
  Expr e = vc_andExprN((VC)vc, (Expr*)arr, (int)numOfChildNodes);
  env->ReleaseLongArrayElements(children, body, 0);
  free(arr);
  return (jlong)e;
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1orExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_orExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1orExprN (JNIEnv *env, jclass clazz, jlong vc, jlongArray children, jint numOfChildNodes)
{
  jlong *body = env->GetLongArrayElements(children, 0);
  Expr* arr = (Expr*)malloc(sizeof(Expr)*(int)numOfChildNodes);  
  for (int i = 0; i < numOfChildNodes; i++){
    arr[i]= (Expr)body[i];
  }
  Expr e = vc_orExprN((VC)vc, (Expr*)arr, (int)numOfChildNodes);
  env->ReleaseLongArrayElements(children, body, 0);
  free(arr);
  return (jlong)e;
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1impliesExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_impliesExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1iffExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_iffExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1iteExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2, jlong e3)
{
  return (jlong)vc_iteExpr((VC)vc, (Expr)e1, (Expr)e2, (Expr)e3);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1boolToBVExpr (JNIEnv *env, jclass clazz, jlong vc, jlong from)
{
  return (jlong)vc_boolToBVExpr((VC)vc, (Expr)from);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1readExpr (JNIEnv *env, jclass clazz, jlong vc, jlong array, jlong index)
{
  return (jlong)vc_readExpr((VC)vc, (Expr)array, (Expr)index);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1writeExpr (JNIEnv *env, jclass clazz, jlong vc, jlong array, jlong index, jlong newvalue)
{
  return (jlong)vc_writeExpr((VC)vc, (Expr)array, (Expr)index, (Expr)newvalue);
}

JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1printExpr (JNIEnv *env, jclass clazz, jlong vc, jlong expr)
{
  vc_printExpr((VC)vc, (Expr)expr);
}

//JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1printExprFile (JNIEnv *env, jclass, jlong, jlong, jint);

JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1printCounterExample (JNIEnv *env, jclass clazz, jlong vc)
{
  vc_printCounterExample((VC)vc);
}

JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1printVarDecls (JNIEnv *env, jclass clazz, jlong vc)
{
  vc_printVarDecls((VC)vc);
}

JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1printAsserts (JNIEnv *env, jclass clazz, jlong vc, jint simplify_print)
{
  vc_printAsserts((VC)vc, (int)simplify_print);
}

JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1printQuery (JNIEnv *env, jclass clazz, jlong vc)
{
  vc_printQuery((VC)vc);
}

JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1assertFormula (JNIEnv *env, jclass clazz, jlong vc, jlong expr)
{
  vc_assertFormula((VC)vc, (Expr)expr);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1simplify (JNIEnv *env, jclass clazz, jlong vc, jlong expr)
{
  return (jlong)vc_simplify((VC)vc, (Expr)expr);
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_vc_1query (JNIEnv *env, jclass clazz, jlong vc, jlong expr)
{
  return (jint)vc_query((VC)vc, (Expr)expr);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1getCounterExample (JNIEnv *env, jclass clazz, jlong vc, jlong expr)
{
  return (jlong)vc_getCounterExample((VC)vc, (Expr)expr);
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_vc_1counterexample_1size (JNIEnv *env, jclass clazz, jlong vc)
{
  return (jint)vc_counterexample_size((VC)vc);
}

JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1push (JNIEnv *env, jclass clazz, jlong vc)
{
  vc_push((VC)vc);
}

JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1pop (JNIEnv *env, jclass clazz, jlong vc)
{
  vc_pop((VC)vc);
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_getBVInt (JNIEnv *env, jclass clazz, jlong expr)
{
  return (jint)getBVInt((Expr)expr);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvType (JNIEnv *env, jclass clazz, jlong vc, jint no_bits)
{
  return (jlong)vc_bvType((VC)vc, (int)no_bits);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bv32Type (JNIEnv *env, jclass clazz, jlong vc)
{
  return (jlong)vc_bv32Type((VC)vc);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvConstExprFromStr (JNIEnv *env, jclass clazz, jlong vc, jstring binary_repr)
{
  jboolean iscopy;
  const char *binary_repr_str = env->GetStringUTFChars(binary_repr, &iscopy);
  jlong result = (jlong)vc_bvConstExprFromStr((VC)vc, const_cast<char*>(binary_repr_str));
  env->ReleaseStringUTFChars(binary_repr, binary_repr_str);
  return result;
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvConstExprFromInt (JNIEnv *env, jclass clazz, jlong vc, jint no_bits, jint value)
{
  return (jlong)vc_bvConstExprFromInt((VC)vc, (int)no_bits, (unsigned int)value);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bv32ConstExprFromInt (JNIEnv *env, jclass clazz, jlong vc, jint value)
{
  return (jlong)vc_bv32ConstExprFromInt((VC)vc, (unsigned int)value);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvConcatExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_bvConcatExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvPlusExpr (JNIEnv *env, jclass clazz, jlong vc, jint no_bits, jlong e1, jlong e2)
{
  return (jlong)vc_bvPlusExpr((VC)vc, (int)no_bits, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bv32PlusExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_bv32PlusExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvMinusExpr (JNIEnv *env, jclass clazz, jlong vc, jint no_bits, jlong e1, jlong e2)
{
  return (jlong)vc_bvMinusExpr((VC)vc, (int)no_bits, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bv32MinusExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_bv32MinusExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvMultExpr (JNIEnv *env, jclass clazz, jlong vc, jint no_bits, jlong e1, jlong e2)
{
  return (jlong)vc_bvMultExpr((VC)vc, (int)no_bits, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bv32MultExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_bv32MultExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvDivExpr (JNIEnv *env, jclass clazz, jlong vc, jint no_bits, jlong e1, jlong e2)
{
  return (jlong)vc_bvDivExpr((VC)vc, (int)no_bits, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvModExpr (JNIEnv *env, jclass clazz, jlong vc, jint no_bits, jlong e1, jlong e2)
{
  return (jlong)vc_bvModExpr((VC)vc, (int)no_bits, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1sbvDivExpr (JNIEnv *env, jclass clazz, jlong vc, jint no_bits, jlong e1, jlong e2)
{
  return (jlong)vc_sbvDivExpr((VC)vc, (int)no_bits, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1sbvModExpr (JNIEnv *env, jclass clazz, jlong vc, jint no_bits, jlong e1, jlong e2)
{
  return (jlong)vc_sbvModExpr((VC)vc, (int)no_bits, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvLtExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_bvLtExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvLeExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_bvLeExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvGtExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_bvGtExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvGeExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_bvGeExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1sbvLtExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_sbvLtExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1sbvLeExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_sbvLeExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1sbvGtExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_sbvGtExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1sbvGeExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_sbvGeExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvUMinusExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1)
{
  return (jlong)vc_bvUMinusExpr((VC)vc, (Expr)e1);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvAndExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_bvAndExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvOrExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_bvOrExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvXorExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e1, jlong e2)
{
  return (jlong)vc_bvXorExpr((VC)vc, (Expr)e1, (Expr)e2);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvNotExpr (JNIEnv *env, jclass clazz, jlong vc, jlong e)
{
  return (jlong)vc_bvNotExpr((VC)vc, (Expr)e);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvLeftShiftExpr (JNIEnv *env, jclass clazz, jlong vc, jint sh_amt, jlong e)
{
  return (jlong)vc_bvLeftShiftExpr((VC)vc, (int)sh_amt, (Expr)e);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvRightShiftExpr (JNIEnv *env, jclass clazz, jlong vc, jint sh_amt, jlong e)
{
  return (jlong)vc_bvRightShiftExpr((VC)vc, (int)sh_amt, (Expr)e);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bv32LeftShiftExpr (JNIEnv *env, jclass clazz, jlong vc, jint sh_amt, jlong e)
{
  return (jlong)vc_bv32LeftShiftExpr((VC)vc, (int)sh_amt, (Expr)e);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bv32RightShiftExpr (JNIEnv *env, jclass clazz, jlong vc, jint sh_amt, jlong e)
{
  return (jlong)vc_bv32RightShiftExpr((VC)vc, (int)sh_amt, (Expr)e);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvVar32LeftShiftExpr (JNIEnv *env, jclass clazz, jlong vc, jlong sh_amt, jlong e)
{
  return (jlong)vc_bvVar32LeftShiftExpr((VC)vc, (Expr)sh_amt, (Expr)e);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvVar32RightShiftExpr (JNIEnv *env, jclass clazz, jlong vc, jlong sh_amt, jlong e)
{
  return (jlong)vc_bvVar32RightShiftExpr((VC)vc, (Expr)sh_amt, (Expr)e);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvVar32DivByPowOfTwoExpr (JNIEnv *env, jclass clazz, jlong vc, jlong child, jlong rhs)
{
  return (jlong)vc_bvVar32DivByPowOfTwoExpr((VC)vc, (Expr)child, (Expr)rhs);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvExtract (JNIEnv *env, jclass clazz, jlong vc, jlong expr, jint high_bit_no, jint low_bit_no)
{
  return (jlong)vc_bvExtract((VC)vc, (Expr)expr, (int)high_bit_no, (int)low_bit_no);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvBoolExtract (JNIEnv *env, jclass clazz, jlong vc, jlong x, jint bit_no)
{
  return (jlong)vc_bvBoolExtract((VC)vc, (Expr)x, (int)bit_no);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvSignExtend (JNIEnv *env, jclass clazz, jlong vc, jlong child, jint nbits)
{
  return (jlong)vc_bvSignExtend((VC)vc, (Expr)child, (int)nbits);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvCreateMemoryArray (JNIEnv *env, jclass clazz, jlong vc, jstring arrayName)
{
  jboolean iscopy;
  const char *arrayNamestr = env->GetStringUTFChars(arrayName, &iscopy);
  jlong result = (jlong)vc_bvCreateMemoryArray((VC)vc, const_cast<char*>(arrayNamestr));
  env->ReleaseStringUTFChars(arrayName, arrayNamestr);
  return result;
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvReadMemoryArray (JNIEnv *env, jclass clazz, jlong vc, jlong array, jlong byteIndex, jint numOfBytes)
{
  return (jlong)vc_bvReadMemoryArray((VC)vc, (Expr)array, (Expr)byteIndex, (int)numOfBytes);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1bvWriteToMemoryArray (JNIEnv *env, jclass clazz, jlong vc, jlong array, jlong byteIndex, jlong element, jint numOfBytes)
{
  return (jlong)vc_bvWriteToMemoryArray((VC)vc, (Expr)array, (Expr)byteIndex, (Expr)element, (int)numOfBytes);
}

JNIEXPORT jstring JNICALL Java_stp_STPJNI_exprString (JNIEnv *env, jclass clazz, jlong e)
{
  char* s = exprString((Expr)e);
  jstring result= env->NewStringUTF(s);
  free(s);
  return result;
}

JNIEXPORT jstring JNICALL Java_stp_STPJNI_typeString (JNIEnv *env, jclass clazz, jlong t)
{
  char* s = typeString((Type)t);
  jstring result= env->NewStringUTF(s);
  free(s);
  return result;
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_getChild (JNIEnv *env, jclass clazz, jlong e, jint i)
{
  return (jlong)getChild((Expr)e, (int)i);
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_vc_1isBool (JNIEnv *env, jclass clazz, jlong e)
{
  return (jint)vc_isBool((Expr)e);
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_vc_1getHashQueryStateToBuffer (JNIEnv *env, jclass clazz, jlong vc, jlong query)
{
  return (jint)vc_getHashQueryStateToBuffer((VC)vc, (Expr)query);
}

JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1Destroy (JNIEnv *env, jclass clazz, jlong vc)
{
  vc_Destroy((VC)vc);
}

JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1DeleteExpr (JNIEnv *env, jclass clazz, jlong e)
{
  vc_DeleteExpr((Expr)e);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1getWholeCounterExample (JNIEnv *env, jclass clazz, jlong vc)
{
  return (jlong)vc_getWholeCounterExample((VC)vc);
}

JNIEXPORT jlong JNICALL Java_stp_STPJNI_vc_1getTermFromCounterExample (JNIEnv *env, jclass clazz, jlong vc, jlong e, jlong c)
{
  return (jlong)vc_getTermFromCounterExample((VC)vc, (Expr)e, (WholeCounterExample)c);
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_getExprKind (JNIEnv *env, jclass clazz, jlong e)
{
  return (jint)getExprKind((Expr)e);
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_getDegree (JNIEnv *env, jclass clazz, jlong e)
{
  return (jint)getDegree((Expr)e);
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_getBVLength (JNIEnv *env, jclass clazz, jlong e)
{
  return (jint)getBVLength((Expr)e);
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_getType (JNIEnv *env, jclass clazz, jlong e)
{
  return (jint)getType((Expr)e);
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_getVWidth (JNIEnv *env, jclass clazz, jlong e)
{
  return (jint)getVWidth((Expr)e);
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_getIWidth (JNIEnv *env, jclass clazz, jlong e)
{
  return (jint)getIWidth((Expr)e);
}

//JNIEXPORT void JNICALL Java_stp_STPJNI_vc_1printCounterExampleFile (JNIEnv *env, jclass clazz, jlong vc, jint fd);

JNIEXPORT jstring JNICALL Java_stp_STPJNI_exprName (JNIEnv *env, jclass clazz, jlong e)
{
  const char* s = exprName((Expr)e);
  jstring result= env->NewStringUTF(s);
  //  free(s);
  return result;
}

JNIEXPORT jint JNICALL Java_stp_STPJNI_getExprID (JNIEnv *env, jclass clazz, jlong e)
{
  return (jint)getExprID((Expr)e);
}




