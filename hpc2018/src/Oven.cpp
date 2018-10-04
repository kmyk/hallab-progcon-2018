//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "Oven.hpp"

//------------------------------------------------------------------------------
#include "Util.hpp"

//------------------------------------------------------------------------------
namespace hpc {

//------------------------------------------------------------------------------
Oven::Oven()
: mRecipe()
, mBakingPieces()
, mLastBakedPieces()
{
}

//------------------------------------------------------------------------------
Oven::Oven(const OvenRecipe& aRecipe)
: mRecipe(aRecipe)
, mBakingPieces()
, mLastBakedPieces()
{
}

//------------------------------------------------------------------------------
bool Oven::isAbleToPut(const Piece& aPiece, const Vector2i& aPos) const
{
    Piece p = aPiece;
    return isAbleToPut(p.width(), p.height(), aPos);
}

//------------------------------------------------------------------------------
bool Oven::isAbleToPut(
    int aPieceWidth,
    int aPieceHeight,
    const Vector2i& aPos
    ) const
{
    return isInArea(aPieceWidth, aPieceHeight, aPos) &&
        isIntersectAnyBakingPiece(aPieceWidth, aPieceHeight, aPos) == false;
}

//------------------------------------------------------------------------------
bool Oven::isInArea(const Piece& aPiece, const Vector2i& aPos) const
{
    Piece p = aPiece;
    return isInArea(p.width(), p.height(), aPos);
}

//------------------------------------------------------------------------------
bool Oven::isInArea(
    int aPieceWidth,
    int aPieceHeight,
    const Vector2i& aPos
    ) const
{
    const int putRight = aPos.x + aPieceWidth - 1;
    const int putBottom = aPos.y + aPieceHeight - 1;
    return 0 <= aPos.x && putRight < width() && 0 <= aPos.y && putBottom < height();
}

//------------------------------------------------------------------------------
bool Oven::isIntersectAnyBakingPiece(const Piece& aPiece, const Vector2i& aPos) const
{
    Piece p = aPiece;
    return isIntersectAnyBakingPiece(p.width(), p.height(), aPos);
}

//------------------------------------------------------------------------------
bool Oven::isIntersectAnyBakingPiece(
    int aPieceWidth,
    int aPieceHeight,
    const Vector2i& aPos
    ) const
{
    for (const auto& bakingPiece : mBakingPieces) {
        if (
            Util::IsIntersect(
                aPos,
                aPieceWidth,
                aPieceHeight,
                bakingPiece.pos(),
                bakingPiece.width(),
                bakingPiece.height()
                )
            )
        {
            // 被っている
            return true;
        }
    }

    // 被っていない
    return false;
}

//------------------------------------------------------------------------------
int Oven::width() const
{
    return mRecipe.width();
}

//------------------------------------------------------------------------------
int Oven::height() const
{
    return mRecipe.height();
}

//------------------------------------------------------------------------------
int Oven::area() const
{
    return mRecipe.area();
}

//------------------------------------------------------------------------------
bool Oven::isEmpty() const
{
    return mBakingPieces.isEmpty();
}

//------------------------------------------------------------------------------
const OvenedPieces& Oven::bakingPieces() const
{
    return mBakingPieces;
}

//------------------------------------------------------------------------------
OvenedPieces& Oven::bakingPieces()
{
    return mBakingPieces;
}

//------------------------------------------------------------------------------
const OvenedPieces& Oven::lastBakedPieces() const
{
    return mLastBakedPieces;
}

//------------------------------------------------------------------------------
OvenedPieces& Oven::lastBakedPieces()
{
    return mLastBakedPieces;
}

//------------------------------------------------------------------------------
void Oven::bakeAndDiscard()
{
    addHeatTurnCount(1);
    clearLastBakedPieces();
    gatherBaked();
}

//------------------------------------------------------------------------------
void Oven::addHeatTurnCount(int aTurnCount)
{
    for (auto& piece : mBakingPieces) {
        piece.addHeatTurnCount(aTurnCount);
    }
}

//------------------------------------------------------------------------------
void Oven::clearLastBakedPieces()
{
    mLastBakedPieces.clear();
}

//------------------------------------------------------------------------------
int Oven::gatherBaked()
{
    int total = 0;

    for (int i = 0; i < mBakingPieces.count(); ++i) {
        auto& piece = mBakingPieces[i];
        if (piece.isCompleted()) {
            total += piece.score();
            mLastBakedPieces.add(piece);
            // 焼き上がった生地を削除、
            // リストの順番に意味は無いので
            // 順番が破壊される代わりに高速に動作する erase を使う
            mBakingPieces.unstableFastErase(i);
            // 末尾の要素が i の位置に移動してきているので、
            // 焼き上がりチェックを再び i の位置からやり直す
            --i;
            continue;
        }
    }

    return total;
}

//------------------------------------------------------------------------------
bool Oven::tryToBake(Piece* aPiece, const Vector2i& aPos)
{
    HPC_ASSERT(aPiece != nullptr);

    // そこに置ける？
    if (isAbleToPut(*aPiece, aPos)) {
    } else {
        // 置けないところに置こうとしています
        return false;
    }

    // 置ける
    aPiece->setPos(aPos);
    mBakingPieces.add(*aPiece);

    return true;
}

} // namespace
// EOF
