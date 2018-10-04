//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "Math.hpp"

//------------------------------------------------------------------------------
#include <cmath>
#include <limits>
#include "Assert.hpp"

//------------------------------------------------------------------------------
namespace hpc {

//------------------------------------------------------------------------------
float Math::Max(float aLhs, float aRhs)
{
    return aLhs > aRhs ? aLhs : aRhs;
}

//------------------------------------------------------------------------------
int Math::Max(int aLhs, int aRhs)
{
    return aLhs > aRhs ? aLhs : aRhs;
}

//------------------------------------------------------------------------------
float Math::Min(float aLhs, float aRhs)
{
    return aLhs < aRhs ? aLhs : aRhs;
}

//------------------------------------------------------------------------------
int Math::Min(int aLhs, int aRhs)
{
    return aLhs < aRhs ? aLhs : aRhs;
}

//------------------------------------------------------------------------------
float Math::LimitMinMax(float aValue, float aMin, float aMax)
{
    return Max(Min(aValue, aMax), aMin);
}

//------------------------------------------------------------------------------
int Math::LimitMinMax(int aValue, int aMin, int aMax)
{
    return Max(Min(aValue, aMax), aMin);
}

//------------------------------------------------------------------------------
float Math::Abs(float aValue)
{
    return aValue >= 0.0f ? aValue : -aValue;
}

//------------------------------------------------------------------------------
int Math::Abs(int aValue)
{
    return aValue >= 0 ? aValue : -aValue;
}

//------------------------------------------------------------------------------
float Math::Sqrt(float aValue)
{
    HPC_ASSERT_GREATER_EQUAL_F(aValue, 0.0f);
    return std::sqrt(aValue);
}

} // namespace
// EOF
