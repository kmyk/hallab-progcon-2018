//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "Util.hpp"

//------------------------------------------------------------------------------
#include "Assert.hpp"

//------------------------------------------------------------------------------
namespace hpc {

//------------------------------------------------------------------------------
bool Util::IsIntersect(
    const Vector2i& aLhsPos,
    int aLhsWidth,
    int aLhsHeight,
    const Vector2i& aRhsPos,
    int aRhsWidth,
    int aRhsHeight
    )
{
    HPC_ASSERT_LESS_EQUAL_I(0, aLhsWidth);
    HPC_ASSERT_LESS_EQUAL_I(0, aLhsHeight);
    HPC_ASSERT_LESS_EQUAL_I(0, aRhsWidth);
    HPC_ASSERT_LESS_EQUAL_I(0, aRhsHeight);

    const Vector2i lhsTerm(aLhsPos + Vector2i(aLhsWidth, aLhsHeight));
    const Vector2i rhsTerm(aRhsPos + Vector2i(aRhsWidth, aRhsHeight));

    return aLhsPos.x < rhsTerm.x &&
        aLhsPos.y < rhsTerm.y &&
        aRhsPos.x < lhsTerm.x &&
        aRhsPos.y < lhsTerm.y;
}

} // namespace
// EOF
