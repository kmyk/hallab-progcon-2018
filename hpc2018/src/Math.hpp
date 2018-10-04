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
namespace hpc {

/// 数学関数群。
class Math
{
public:
    /// @name 数値関係
    //@{
    /// 二値のうち大きい方を返します。
    static float Max(float aLhs, float aRhs);
    /// 二値のうち大きい方を返します。
    static int Max(int aLhs, int aRhs);
    /// 二値のうち小さい方を返します。
    static float Min(float aLhs, float aRhs);
    /// 二値のうち小さい方を返します。
    static int Min(int aLhs, int aRhs);
    /// aValue の値を指定の範囲 [aMin, aMax] に制限します。
    static float LimitMinMax(float aValue, float aMin, float aMax);
    /// aValue の値を指定の範囲 [aMin, aMax] に制限します。
    static int LimitMinMax(int aValue, int aMin, int aMax);
    /// 値の絶対値を返します。
    static float Abs(float aValue);
    /// 値の絶対値を返します。
    static int Abs(int aValue);
    /// 値の平方根を求めます。
    static float Sqrt(float aValue);
    //@}

private:
    Math();
};

} // namespace
// EOF
