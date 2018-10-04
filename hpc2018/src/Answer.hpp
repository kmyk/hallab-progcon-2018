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
#include "Action.hpp"
#include "Array.hpp"
#include "ArrayNum.hpp"
#include "Assert.hpp"
#include "Math.hpp"
#include "Print.hpp"
#include "Stage.hpp"
#include "Util.hpp"
#include "Vector2i.hpp"

//------------------------------------------------------------------------------
namespace hpc {

/// ゲームへの解答。
/// @detail 参加者は Answer.cpp にこのクラスのメンバ関数を実装することで、
///         プログラムを作成してください。
class Answer
{
public:
    /// @name コンストラクタ/デストラクタ
    //@{
    Answer();
    ~Answer();
    //@}

    /// @name 解答
    //@{
    /// 各ステージ開始時に呼び出される処理。
    void init(const Stage& aStage);
    /// 各ターンの行動を決定する。
    Action decideNextAction(const Stage& aStage);
    /// 各ステージ終了時に呼び出される処理。
    void finalize(const Stage& aStage);
    //@}
};

} // namespace
// EOF
