//
// HAL Programming Contest 2018 Viewer
// Copyright (c) 2018 HAL Laboratory, Inc.
//
'use strict';
const vm = new Vue({
  el: 'body',
  data: {
    json: true,
    stage: 0, turn: 0,
    playType: 0, isPlay: false, timer: null, isDrag: false,
    badColorScore: 20000, goodColorScore: 160000
  },
  created: function () {
    if (location.href.match(/(?:\?|&)data=/)) this.importparam();
  },
  computed: {
    totalTurn: function () { return this.json[0]; },
    totalScore: function () { return this.json[1]; },
    turnLimit: function () { return this.json[2][0]; },
    stages: function () { return this.json[3]; },
    ovenConfigs: function () { return this.stages[this.stage][2][0]; },
    turns: function () { return this.stages[this.stage][3]; },
    candidates: function () { return this.turns[this.turn][2]; },
    ovens: function () { return this.turns[this.turn][3]; }
  },
  methods: {
    reset: function (e) { e.target.value = null; },
    getParameterByName: function(name) {
      name = name.replace(/[\[]/, "\\\[").replace(/[\]]/, "\\\]");
      var regex = new RegExp("[\\?&]" + name + "=([^&#]*)"),
          results = regex.exec(location.search);
      return results == null ? "" : decodeURIComponent(results[1].replace(/\+/g, " "));
    },
    // <input type="file">からjsonファイルが選択された時に呼ばれる
    import: function (e) {
      const reader = new FileReader();
      reader.onload = (function () {
        return function (e) {
          try {
            vm.json = JSON.parse(e.target.result);
            vm.stage = 0;
          } catch (ee) {
            alert('JSONファイルが壊れています');
          }
        }
      })(e.target.files[0]);
      reader.readAsText(e.target.files[0]);
    },
    // urlの引数で data=[jsonファイルのパス] が指定されている時に呼ばれる
    importparam: function (e) {
      var xhr = new XMLHttpRequest();
      xhr.open('GET', this.getParameterByName('data'));
      xhr.onreadystatechange = function () {
        if (xhr.readyState === 4) {
          if (xhr.status === 200 || xhr.status === 0) {
            try {
              vm.json = JSON.parse(xhr.responseText);
              vm.stage = 0;
            } catch (ee) {
              alert('JSONファイルが壊れています');
            }
          } else if(xhr.status === 404) {
            alert('JSONファイルが見つかりません');
          }
        }
      };
      xhr.send(null);
    },
    drag: function (e) {
      const sliderRect = e.target.parentNode.getBoundingClientRect();
      this.turn = (e.clientX - sliderRect.left)*this.turns.length/sliderRect.width|0;
      this.isDrag = true;
    },
    stageColor: function (no) {
      let score = this.stages[no][1],
          weight = (score - this.badColorScore)/(this.goodColorScore - this.badColorScore);
      weight = Math.min(Math.max(weight, 0), 1);
      return 'hsl(' + (weight*120|0) + ', 100%, 50%)';
    },
    ovenStyle: function (no) {
      const oven = this.ovenConfigs[no];
      return { height: oven[1]*10 + 'px', width: oven[0]*10 + 'px' };
    },
    candidatePieceStyle: function (laneNo, pieceNo) {
      const piece = this.candidates[laneNo][pieceNo];
      return { height: piece[2]*10 + 'px', width: piece[1]*10 + 'px' };
    },
    bakingPieceStyle: function (ovenNo, pieceNo) {
      const piece = this.ovens[ovenNo][1][pieceNo],
            x = piece[0][0], y = piece[0][1], w = piece[1], h = piece[2],
            r = piece[3]/piece[4];
      return {
        background: 'hsl(' + ((1 - r)*60|0) + ', 100%, 75%)',
        height: h*10 + 'px', left: x*10 + 'px', top: y*10 + 'px', width: w*10 + 'px'
      };
    }
  },
  watch: {
    stage: function (stage) {
      this.stage = Math.min(Math.max(stage, 0), this.stages.length - 1);
      this.turn = 0;
    },
    turn: function (turn) {
      const slider = document.getElementById('slider'),
            control = slider.firstChild.nextSibling;
      this.turn = Math.min(Math.max(turn, 0), this.turns.length - 1);
      control.style.left = (
        (slider.getBoundingClientRect().width - control.getBoundingClientRect().width)
        *this.turn/(this.turns.length - 1)|0
      ) + 'px';
    },
    isPlay: function (isPlay) {
      var frame = 50;
      if (isPlay) {
        this.timer = setTimeout(function loop() {
          if (vm.turn < vm.turns.length - 1) {
            vm.turn++;
            vm.timer = setTimeout(loop, frame);
          } else if (vm.playType == 1) {
            vm.turn = 0;
            vm.timer = setTimeout(loop, frame);
          } else if(vm.playType == 2) {
            if (vm.stage < vm.stages.length - 1) {
              vm.stage++
            } else vm.stage = 0;
            vm.timer = setTimeout(loop, frame);
          } else vm.isPlay = false;
        }, frame);
      } else clearTimeout(this.timer);
    }
  }
})
