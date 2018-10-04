//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "Piece.hpp"

//------------------------------------------------------------------------------
#include "Assert.hpp"

//------------------------------------------------------------------------------
namespace hpc {

//------------------------------------------------------------------------------
Piece::Piece()
: mPos()
, mWidth()
, mHeight()
, mCurrentHeatTurnCount()
, mRequiredHeatTurnCount()
, mScore()
{
}

//------------------------------------------------------------------------------
Piece::Piece(
    const Vector2i& aPos,
    int aWidth,
    int aHeight,
    int aRequiredHeatTurnCount,
    int aScore
    )
: mPos(aPos)
, mWidth(aWidth)
, mHeight(aHeight)
, mCurrentHeatTurnCount()
, mRequiredHeatTurnCount(aRequiredHeatTurnCount)
, mScore(aScore)
{
    HPC_ASSERT_GREATER_I(mScore, 0);
    HPC_ASSERT_GREATER_I(mRequiredHeatTurnCount, 0);
}

//------------------------------------------------------------------------------
Vector2i Piece::pos() const
{
    return mPos;
}

//------------------------------------------------------------------------------
int Piece::width() const
{
    return mWidth;
}

//------------------------------------------------------------------------------
int Piece::height() const
{
    return mHeight;
}

//------------------------------------------------------------------------------
int Piece::currentHeatTurnCount() const
{
    return mCurrentHeatTurnCount;
}

//------------------------------------------------------------------------------
int Piece::requiredHeatTurnCount() const
{
    return mRequiredHeatTurnCount;
}

//------------------------------------------------------------------------------
int Piece::restRequiredHeatTurnCount() const
{
    return requiredHeatTurnCount() - currentHeatTurnCount();
}

//------------------------------------------------------------------------------
int Piece::score() const
{
    return mScore;
}

//------------------------------------------------------------------------------
void Piece::setPos(const Vector2i& aPos)
{
    mPos = aPos;
}

//------------------------------------------------------------------------------
void Piece::addHeatTurnCount(int aTurnCount)
{
    mCurrentHeatTurnCount += aTurnCount;
}

//------------------------------------------------------------------------------
bool Piece::isCompleted() const
{
    return mRequiredHeatTurnCount <= mCurrentHeatTurnCount;
}

} // namespace
// EOF
