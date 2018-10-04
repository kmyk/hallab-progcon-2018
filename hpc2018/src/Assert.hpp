//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once

//------------------------------------------------------------------------------
#include <cassert>
#include <cstdio>

//------------------------------------------------------------------------------
/// メッセージ付きアサート。
/// @detail 条件を満たさない場合に任意のメッセージを表示して停止する、
///         プログラムの検証用アサートです。
/// @param aExp 条件式。
/// @param ... 書式。引数の設定方法は std::printf に準じます。
#define HPC_ASSERT_MSG(aExp, ...) \
    do { \
        if (!(aExp)) { \
            std::printf(__VA_ARGS__); \
            std::printf("\n"); \
            assert(aExp); \
        } \
    } while (false)

//------------------------------------------------------------------------------
/// 標準のアサート。
/// @detail 条件式が true になることを表明します。
///         条件式が true にならなかった場合、既定のメッセージを表示して停止します。
/// @param aExp 条件式。
#define HPC_ASSERT(aExp) HPC_ASSERT_MSG(aExp, "Assertion Failed")

//------------------------------------------------------------------------------
/// (整数専用) aValue1 <= aValue2 であることを表明するアサート。
/// @note 整数専用です。それ以外の型を使うと、判定は動作しますがメッセージが壊れます。
#define HPC_ASSERT_LESS_EQUAL_I(aValue1, aValue2) \
    HPC_ASSERT_MSG( \
        aValue1 <= aValue2, \
        "<%s>(%d) should be less than or equal to <%s>(%d).", \
        #aValue1, aValue1, #aValue2, aValue2)

//------------------------------------------------------------------------------
/// (float専用) aValue1 <= aValue2 であることを表明するアサート。
/// @note float専用です。それ以外の型を使うと、判定は動作しますがメッセージが壊れます。
#define HPC_ASSERT_LESS_EQUAL_F(aValue1, aValue2) \
    HPC_ASSERT_MSG( \
        aValue1 <= aValue2, \
        "<%s>(%f) should be less than or equal to <%s>(%f).", \
        #aValue1, aValue1, #aValue2, aValue2)

//------------------------------------------------------------------------------
/// (整数専用) aValue1 < aValue2 であることを表明するアサート。
/// @note 整数専用です。それ以外の型を使うと、判定は動作しますがメッセージが壊れます。
#define HPC_ASSERT_LESS_I(aValue1, aValue2) \
    HPC_ASSERT_MSG( \
        aValue1 < aValue2, \
        "<%s>(%d) should be less than or equal to <%s>(%d).", \
        #aValue1, aValue1, #aValue2, aValue2)

//------------------------------------------------------------------------------
/// (float専用) aValue1 < aValue2 であることを表明するアサート。
/// @note float専用です。それ以外の型を使うと、判定は動作しますがメッセージが壊れます。
#define HPC_ASSERT_LESS_F(aValue1, aValue2) \
    HPC_ASSERT_MSG( \
        aValue1 < aValue2, \
        "<%s>(%f) should be less than <%s>(%f).", \
        #aValue1, aValue1, #aValue2, aValue2)

//------------------------------------------------------------------------------
/// (整数専用) aValue1 > aValue2 であることを表明するアサート。
/// @note 整数専用です。それ以外の型を使うと、判定は動作しますがメッセージが壊れます。
#define HPC_ASSERT_GREATER_I(aValue1, aValue2) \
    HPC_ASSERT_MSG( \
        aValue1 > aValue2, \
        "<%s>(%d) should be greater than <%s>(%d).", \
        #aValue1, aValue1, #aValue2, aValue2)

//------------------------------------------------------------------------------
/// (float専用) aValue1 > aValue2 であることを表明するアサート。
/// @note float専用です。それ以外の型を使うと、判定は動作しますがメッセージが壊れます。
#define HPC_ASSERT_GREATER_F(aValue1, aValue2) \
    HPC_ASSERT_MSG( \
        aValue1 > aValue2, \
        "<%s>(%f) should be greater than <%s>(%f).", \
        #aValue1, aValue1, #aValue2, aValue2)

//------------------------------------------------------------------------------
/// (整数専用) aValue1 >= aValue2 であることを表明するアサート。
/// @note 整数専用です。それ以外の型を使うと、判定は動作しますがメッセージが壊れます。
#define HPC_ASSERT_GREATER_EQUAL_I(aValue1, aValue2) \
    HPC_ASSERT_MSG( \
        aValue1 >= aValue2, \
        "<%s>(%d) should be greater than or equal to <%s>(%d).", \
        #aValue1, aValue1, #aValue2, aValue2)

//------------------------------------------------------------------------------
/// (float専用) aValue1 >= aValue2 であることを表明するアサート。
/// @note float専用です。それ以外の型を使うと、判定は動作しますがメッセージが壊れます。
#define HPC_ASSERT_GREATER_EQUAL_F(aValue1, aValue2) \
    HPC_ASSERT_MSG( \
        aValue1 >= aValue2, \
        "<%s>(%f) should be greater than or equal to <%s>(%f).", \
        #aValue1, aValue1, #aValue2, aValue2)

//------------------------------------------------------------------------------
/// (整数専用) aMin <= aValue < aTerm であることを表明するアサート。
/// @note 整数専用です。それ以外の型を使うと、判定は動作しますがメッセージが壊れます。
#define HPC_ASSERT_MIN_TERM_I(aValue, aMin, aTerm) \
    HPC_ASSERT_MSG( \
        aMin <= aValue && aValue < aTerm, \
        "<%s>(%d) is out of range [%d, %d)", \
        #aValue, aValue, aMin, aTerm)

//------------------------------------------------------------------------------
/// (整数専用) aMin <= aValue <= aMax であることを表明するアサート。
/// @note 整数専用です。それ以外の型を使うと、判定は動作しますがメッセージが壊れます。
#define HPC_ASSERT_MIN_MAX_I(aValue, aMin, aMax) \
    HPC_ASSERT_MSG( \
        aMin <= aValue && aValue <= aMax, \
        "<%s>(%d) is out of range [%d, %d]", \
        #aValue, aValue, aMin, aMax)

//------------------------------------------------------------------------------
/// 列挙型制限アサート。
/// @detail 列挙型の値が有効な範囲内であることを表明します。
/// @pre 列挙型の開始値が 0 であり、かつ終端値が Typename_TERM の形で宣言されている。
/// @param aType 列挙型の型。
/// @param aValue 検査する値。
#define HPC_ASSERT_ENUM(aType, aValue) \
    HPC_ASSERT_MSG( \
        0 <= aValue && aValue < aType ## _TERM, \
        "aValue %d is out of range: %s[0,%d]", \
        aValue, #aType "_TERM", aType ## _TERM)

//------------------------------------------------------------------------------
/// 到達禁止アサート。
/// @detail プログラムが現在位置に到達しないことを表明します。
///         到達してしまった場合はメッセージを表示して停止します。
#define HPC_ASSERT_NOT_REACHED() HPC_ASSERT_MSG(false, "Should not reach here.")

//------------------------------------------------------------------------------
/// メッセージ付き到達禁止アサート。
/// @detail プログラムが現在位置に到達しないことを表明します。
///         到達してしまった場合はメッセージを表示して停止します。
#define HPC_ASSERT_NOT_REACHED_MSG(...) HPC_ASSERT_MSG(false, __VA_ARGS__)

// EOF
