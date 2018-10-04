//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "Action.hpp"

//------------------------------------------------------------------------------
namespace hpc {

//------------------------------------------------------------------------------
Action Action::Put(
    CandidateLaneType aCandidateLaneType,
    int aPieceIndex,
    const Vector2i& aPutPos
    )
{
    Action action;
    action.mType = ActionType_Put;
    action.mCandidateLaneType = aCandidateLaneType;
    action.mPieceIndex = aPieceIndex;
    action.mPutPos = aPutPos;
    return action;
}

//------------------------------------------------------------------------------
Action Action::Wait()
{
    Action action;
    action.mType = ActionType_Wait;
    return action;
}

//------------------------------------------------------------------------------
Action::Action()
: mType(ActionType_Wait)
, mCandidateLaneType(CandidateLaneType_Small)
, mPieceIndex()
, mPutPos()
{
}

//------------------------------------------------------------------------------
ActionType Action::type() const
{
    return mType;
}

//------------------------------------------------------------------------------
bool Action::isWaiting() const
{
    return type() == ActionType_Wait;
}

//------------------------------------------------------------------------------
CandidateLaneType Action::candidateLaneType() const
{
    return mCandidateLaneType;
}

//------------------------------------------------------------------------------
int Action::pieceIndex() const
{
    return mPieceIndex;
}

//------------------------------------------------------------------------------
Vector2i Action::putPos() const
{
    return mPutPos;
}

} // namespace
// EOF
