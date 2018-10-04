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
#include "Answer.hpp"
#include "Random.hpp"
#include "Recorder.hpp"
#include "Timer.hpp"

//------------------------------------------------------------------------------
namespace hpc {

/// ゲーム全体。
class Game
{
public:
    /// @name コンストラクタ
    //@{
    Game();
    //@}

    /// @name 設定
    //@{
    /// 乱数シードを変更する。
    void changeSeed(RandomSeed aSeed);
    //@}

    /// @name 実行
    //@{
    /// ゲームを実行する。
    void run(Answer* aAnswer);
    //@}

    /// @name 問い合わせ
    //@{
    const Recorder& recorder() const;
    const Timer& timer() const;
    //@}

private:
    /// @name プライベートメンバ変数
    //@{
    /// 外部から乱数シードを設定された状態か。
    bool mIsRandomSeedSet;
    /// 外部から設定された乱数シード。
    RandomSeed mGivenRandomSeed;
    Recorder mRecorder;
    Timer mTimer;
    //@}
};

} // namespace
// EOF
