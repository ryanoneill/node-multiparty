var stream = require('stream');
var util = require('util');
var fs = require('fs');
var crypto = require('crypto');
var path = require('path');
var os = require('os');
var StringDecoder = require('string_decoder').StringDecoder;
var fdSlicer = require('fd-slicer');

var START = 0;
var START_BOUNDARY = 1;
var HEADER_FIELD_START = 2;
var HEADER_FIELD = 3;
var HEADER_VALUE_START = 4;
var HEADER_VALUE = 5;
var HEADER_VALUE_ALMOST_DONE = 6;
var HEADERS_ALMOST_DONE = 7;
var PART_DATA_START = 8;
var PART_DATA = 9;
// var PART_END = 10;
var CLOSE_BOUNDARY = 11;
var END = 12;

var LF = 10;
var CR = 13;
var SPACE = 32;
var HYPHEN = 45;
var COLON = 58;
var A = 97;
var Z = 122;

var CONTENT_TYPE_RE = /^multipart\/(?:form-data|related)(?:;|$)/i;
var CONTENT_TYPE_PARAM_RE = /;\s*([^=]+)=(?:"([^"]+)"|([^;]+))/gi;
var FILE_EXT_RE = /(\.[_\-a-zA-Z0-9]{0,16}).*/;
var LAST_BOUNDARY_SUFFIX_LEN = 4; // --\r\n

// replace base64 characters with safe-for-filename characters
var b64Safe = {'/': '_', '+': '-'};

exports.Form = Form;

util.inherits(Form, stream.Writable);
function Form(options) {
  var self = this;
  stream.Writable.call(self);

  options = options || {};

  self.error = null;

  self.autoFields = !!options.autoFields;
  self.autoFiles = !!options.autoFiles;

  self.maxFields = options.maxFields || 1000;
  self.maxFieldsSize = options.maxFieldsSize || 2 * 1024 * 1024;
  self.maxFilesSize = options.maxFilesSize || Infinity;
  self.uploadDir = options.uploadDir || os.tmpDir();
  self.encoding = options.encoding || 'utf8';

  self.bytesReceived = 0;
  self.bytesExpected = null;

  self.openedFiles = [];
  self.totalFieldSize = 0;
  self.totalFieldCount = 0;
  self.totalFileSize = 0;
  self.flushing = 0;

  self.backpressure = false;
  self.writeCbs = [];

  self.emitQueue = [];

  self.on('newListener', function (eventName) {
    if (eventName === 'file') {
      self.autoFiles = true;
    } else if (eventName === 'field') {
      self.autoFields = true;
    }
  });
}

Form.prototype.parse = function (req, cb) {
  var called = false;
  var self = this;
  var waitend = true;

  if (cb) {
    // if the user supplies a callback, this implies autoFields and autoFiles
    self.autoFields = true;
    self.autoFiles = true;

    // wait for request to end before calling cb
    var end = function (done) {
      if (called) return;

      called = true;

      // wait for req events to fire
      process.nextTick(function () {
        if (waitend && req.readable) {
          // dump rest of request
          req.resume();
          req.once('end', done);
          return;
        }

        done();
      });
    };

    var fields = {};
    var files = {};
    self.on('error', function (err) {
      end(function () {
        cb(err);
      });
    });
    self.on('field', function (name, value) {
      var fieldsArray = fields[name] || (fields[name] = []);
      fieldsArray.push(value);
    });
    self.on('file', function (name, file) {
      var filesArray = files[name] || (files[name] = []);
      filesArray.push(file);
    });
    self.on('close', function () {
      end(function () {
        cb(null, fields, files);
      });
    });
  }

  self.handleError = handleError;
  self.bytesExpected = getBytesExpected(req.headers);

  req.on('end', onReqEnd);
  req.on('error', function (err) {
    waitend = false;
    handleError(err);
  });
  req.on('aborted', onReqAborted);

  var state = req._readableState;
  if (req._decoder || (state && (state.encoding || state.decoder))) {
    // this is a binary protocol
    // if an encoding is set, input is likely corrupted
    validationError(new Error('request encoding must not be set'));
    return;
  }

  var contentType = req.headers['content-type'];
  if (!contentType) {
    validationError(createError(415, 'missing content-type header'));
    return;
  }

  var m = CONTENT_TYPE_RE.exec(contentType);
  if (!m) {
    validationError(createError(415, 'unsupported content-type'));
    return;
  }

  var boundary;
  CONTENT_TYPE_PARAM_RE.lastIndex = m.index + m[0].length - 1;
  while ((m = CONTENT_TYPE_PARAM_RE.exec(contentType))) {
    if (m[1].toLowerCase() !== 'boundary') continue;
    boundary = m[2] || m[3];
    break;
  }

  if (!boundary) {
    validationError(createError(400, 'content-type missing boundary'));
    return;
  }

  setUpParser(self, boundary);
  req.pipe(self);

  function onReqAborted() {
    waitend = false;
    self.emit('aborted');
    handleError(new Error('Request aborted'));
  }

  function onReqEnd() {
    waitend = false;
  }

  function handleError(err) {
    var first = !self.error;
    if (first) {
      self.error = err;
      req.removeListener('aborted', onReqAborted);
      req.removeListener('end', onReqEnd);
      if (self.destStream) {
        errorEventQueue(self, self.destStream, err);
      }
    }

    cleanupOpenFiles(self);

    if (first) {
      self.emit('error', err);
    }
  }

  function validationError(err) {
    // handle error on next tick for event listeners to attach
    process.nextTick(handleError.bind(null, err));
  }
};

Form.prototype._write = function (buffer, encoding, cb) {
  if (this.error) return;

  var self = this;
  var i = 0;
  var c;
  var bufferLength = buffer.length;

  var st = {
    prevIndex: self.index,
    index: self.index,
    state: self.state,
    lookbehind: self.lookbehind,
    boundary: self.boundary,
    boundaryChars: self.boundaryChars,
    boundaryLength: self.boundary.length,
    boundaryEnd: self.boundary.length - 1
  };

  function handleStart(st) {
    st.index = 0;
    st.state = START_BOUNDARY;
    return undefined;
  }

  function handleStartBoundary(st) {
    if (st.index === st.boundaryLength - 2 && c === HYPHEN) {
      st.index = 1;
      st.state = CLOSE_BOUNDARY;
      return undefined;
    } else if (st.index === st.boundaryLength - 2) {
      if (c !== CR) {
        return self.handleError(createError(400, 'Expected CR Received ' + c));
      }
      st.index++;
      return undefined;
    } else if (st.index === st.boundaryLength - 1) {
      if (c !== LF) {
        return self.handleError(createError(400, 'Expected LF Received ' + c));
      }
      st.index = 0;
      self.onParsePartBegin();
      st.state = HEADER_FIELD_START;
      return undefined;
    }

    if (c !== st.boundary[st.index + 2]) st.index = -2;
    if (c === st.boundary[st.index + 2]) st.index++;
    return undefined;
  }

  function handleHeaderFieldStart(st) {
    st.state = HEADER_FIELD;
    self.headerFieldMark = i;
    st.index = 0;
    return undefined;
  }

  function handleHeaderField(st) {
    if (c === CR) {
      self.headerFieldMark = null;
      st.state = HEADERS_ALMOST_DONE;
      return undefined;
    }

    st.index++;
    if (c === HYPHEN) {
      return undefined;
    }

    if (c === COLON) {
      if (st.index === 1) {
        // empty header field
        self.handleError(createError(400, 'Empty header field'));
        return;
      }
      self.onParseHeaderField(buffer.slice(self.headerFieldMark, i));
      self.headerFieldMark = null;
      st.state = HEADER_VALUE_START;
      return undefined;
    }

    var cl = lower(c);
    if (cl < A || cl > Z) {
      self.handleError(createError(400,
        'Expected alphabetic character, received ' + c));
      return;
    }
    return undefined;
  }

  function handleHeaderValueStart(st) {
    if (c === SPACE) {
      return undefined;
    }

    self.headerValueMark = i;
    st.state = HEADER_VALUE;
    return undefined;
  }

  function handleHeaderValue(st) {
    if (c === CR) {
      self.onParseHeaderValue(buffer.slice(self.headerValueMark, i));
      self.headerValueMark = null;
      self.onParseHeaderEnd();
      st.state = HEADER_VALUE_ALMOST_DONE;
    }
    return undefined;
  }

  function handleHeaderValueAlmostDone(st) {
    if (c !== LF) {
      return self.handleError(createError(400,
        'Expected LF Received ' + c));
    }
    st.state = HEADER_FIELD_START;
    return undefined;
  }

  function handleHeadersAlmostDone(st) {
    if (c !== LF) {
      return self.handleError(createError(400,
        'Expected LF Received ' + c));
    }
    var err = self.onParseHeadersEnd(i + 1);
    if (err) return self.handleError(err);
    st.state = PART_DATA_START;
    return undefined;
  }

  function handlePartDataStart(st) {
    st.state = PART_DATA;
    self.partDataMark = i;
    return undefined;
  }

  function handlePartData(st) {
    st.prevIndex = st.index;

    if (st.index === 0) {
      // boyer-moore derrived algorithm to safely skip non-boundary data
      i += st.boundaryEnd;
      while (i < bufferLength && !(buffer[i] in st.boundaryChars)) {
        i += st.boundaryLength;
      }
      i -= st.boundaryEnd;
      c = buffer[i];
    }

    if (st.index < st.boundaryLength) {
      if (st.boundary[st.index] === c) {
        if (st.index === 0) {
          self.onParsePartData(buffer.slice(self.partDataMark, i));
          self.partDataMark = null;
        }
        st.index++;
      } else {
        st.index = 0;
      }
    } else if (st.index === st.boundaryLength) {
      st.index++;
      if (c === CR) {
        // CR = part boundary
        self.partBoundaryFlag = true;
      } else if (c === HYPHEN) {
        st.index = 1;
        st.state = CLOSE_BOUNDARY;
        return undefined;
      } else {
        st.index = 0;
      }
    } else if (st.index - 1 === st.boundaryLength) {
      if (self.partBoundaryFlag) {
        st.index = 0;
        if (c === LF) {
          self.partBoundaryFlag = false;
          self.onParsePartEnd();
          self.onParsePartBegin();
          st.state = HEADER_FIELD_START;
          return undefined;
        }
      } else {
        st.index = 0;
      }
    }

    if (st.index > 0) {
      // when matching a possible boundary, keep a lookbehind reference
      // in case it turns out to be a false lead
      st.lookbehind[st.index - 1] = c;
    } else if (st.prevIndex > 0) {
      // if our boundary turned out to be rubbish, the captured lookbehind
      // belongs to partData
      self.onParsePartData(st.lookbehind.slice(0, st.prevIndex));
      st.prevIndex = 0;
      self.partDataMark = i;

      // reconsider the current character
      // even so it interrupted the sequence
      // it could be the beginning of a new sequence
      i--;
    }
    return undefined;
  }

  function handleCloseBoundary(st) {
    if (c !== HYPHEN) {
      return self.handleError(createError(400,
        'Expected HYPHEN Received ' + c));
    }
    if (st.index === 1) {
      self.onParsePartEnd();
      st.state = END;
    } else if (st.index > 1) {
      return self.handleError(new Error('Parser has invalid state.'));
    }
    st.index++;
    return undefined;
  }

  var result;
  for (i = 0; i < bufferLength; i++) {
    c = buffer[i];
    switch (st.state) {
      case START:
        result = handleStart(st);
        if (result) return result;
        /* falls through */
      case START_BOUNDARY:
        result = handleStartBoundary(st);
        if (result) return result;
        break;
      case HEADER_FIELD_START:
        result = handleHeaderFieldStart(st);
        if (result) return result;
        /* falls through */
      case HEADER_FIELD:
        result = handleHeaderField(st);
        if (result) return result;
        break;
      case HEADER_VALUE_START:
        result = handleHeaderValueStart(st);
        if (result) return result;
        /* falls through */
      case HEADER_VALUE:
        result = handleHeaderValue(st);
        if (result) return result;
        break;
      case HEADER_VALUE_ALMOST_DONE:
        result = handleHeaderValueAlmostDone(st);
        if (result) return result;
        break;
      case HEADERS_ALMOST_DONE:
        result = handleHeadersAlmostDone(st);
        if (result) return result;
        break;
      case PART_DATA_START:
        result = handlePartDataStart(st);
        if (result) return result;
        /* falls through */
      case PART_DATA:
        result = handlePartData(st);
        if (result) return result;
        break;
      case CLOSE_BOUNDARY:
        result = handleCloseBoundary(st);
        if (result) return result;
        break;
      case END:
        break;
      default:
        self.handleError(new Error('Parser has invalid state.'));
        return;
    }
  }

  if (self.headerFieldMark != null) {
    self.onParseHeaderField(buffer.slice(self.headerFieldMark));
    self.headerFieldMark = 0;
  }
  if (self.headerValueMark != null) {
    self.onParseHeaderValue(buffer.slice(self.headerValueMark));
    self.headerValueMark = 0;
  }
  if (self.partDataMark != null) {
    self.onParsePartData(buffer.slice(self.partDataMark));
    self.partDataMark = 0;
  }

  self.index = st.index;
  self.state = st.state;

  self.bytesReceived += buffer.length;
  self.emit('progress', self.bytesReceived, self.bytesExpected);

  if (self.backpressure) {
    self.writeCbs.push(cb);
  } else {
    cb();
  }
};

Form.prototype.onParsePartBegin = function () {
  clearPartVars(this);
};

Form.prototype.onParseHeaderField = function (b) {
  this.headerField += this.headerFieldDecoder.write(b);
};

Form.prototype.onParseHeaderValue = function (b) {
  this.headerValue += this.headerValueDecoder.write(b);
};

Form.prototype.onParseHeaderEnd = function () {
  this.headerField = this.headerField.toLowerCase();
  this.partHeaders[this.headerField] = this.headerValue;

  var m;
  if (this.headerField === 'content-disposition') {
    m = this.headerValue.match(/\bname="([^"]+)"/i);
    if (m) {
      this.partName = m[1];
    }
    this.partFilename = parseFilename(this.headerValue);
  } else if (this.headerField === 'content-transfer-encoding') {
    this.partTransferEncoding = this.headerValue.toLowerCase();
  }

  this.headerFieldDecoder = new StringDecoder(this.encoding);
  this.headerField = '';
  this.headerValueDecoder = new StringDecoder(this.encoding);
  this.headerValue = '';
};

Form.prototype.onParsePartData = function (b) {
  if (this.partTransferEncoding === 'base64') {
    this.backpressure = !this.destStream.write(b.toString('ascii'), 'base64');
  } else {
    this.backpressure = !this.destStream.write(b);
  }
};

Form.prototype.onParsePartEnd = function () {
  if (this.destStream) {
    flushWriteCbs(this);
    var s = this.destStream;
    process.nextTick(function () {
      s.end();
    });
  }
  clearPartVars(this);
};

Form.prototype.onParseHeadersEnd = function (offset) {
  var self = this;
  switch (self.partTransferEncoding) {
    case 'binary':
    case '7bit':
    case '8bit':
    self.partTransferEncoding = 'binary';
    break;

    case 'base64': break;
    default:
    return createError(400, 'unknown transfer-encoding: ' +
      self.partTransferEncoding);
  }

  self.totalFieldCount += 1;
  if (self.totalFieldCount > self.maxFields) {
    return createError(413, 'maxFields ' + self.maxFields + ' exceeded.');
  }

  self.destStream = new stream.PassThrough();
  self.destStream.on('drain', function () {
    flushWriteCbs(self);
  });
  self.destStream.headers = self.partHeaders;
  self.destStream.name = self.partName;
  self.destStream.filename = self.partFilename;
  self.destStream.byteOffset = self.bytesReceived + offset;
  var partContentLength = self.destStream.headers['content-length'];
  self.destStream.byteCount = partContentLength ?
    parseInt(partContentLength, 10) :
    self.bytesExpected ? (self.bytesExpected - self.destStream.byteOffset -
      self.boundary.length - LAST_BOUNDARY_SUFFIX_LEN) :
    undefined;

  if (self.destStream.filename == null && self.autoFields) {
    handleField(self, self.destStream);
  } else if (self.destStream.filename != null && self.autoFiles) {
    handleFile(self, self.destStream);
  } else {
    handlePart(self, self.destStream);
  }
};

function flushWriteCbs(self) {
  self.writeCbs.forEach(function (cb) {
    process.nextTick(cb);
  });
  self.writeCbs = [];
  self.backpressure = false;
}

function getBytesExpected(headers) {
  var contentLength = headers['content-length'];
  if (contentLength) {
    return parseInt(contentLength, 10);
  } else if (headers['transfer-encoding'] == null) {
    return 0;
  } else {
    return null;
  }
}

function beginFlush(self) {
  self.flushing += 1;
}

function endFlush(self) {
  self.flushing -= 1;

  if (self.flushing < 0) {
    // if this happens this is a critical bug in multiparty and this stack trace
    // will help us figure it out.
    self.handleError(new Error('unexpected endFlush'));
    return;
  }

  maybeClose(self);
}

function maybeClose(self) {
  if (self.flushing > 0 || self.error) return;

  // go through the emit queue in case any field, file, or part events are
  // waiting to be emitted
  holdEmitQueue(self)(function () {
    // nextTick because the user is listening to part 'end' events and we are
    // using part 'end' events to decide when to emit 'close'. we add our 'end'
    // handler before the user gets a chance to add theirs. So we make sure
    // their 'end' event fires before we emit the 'close' event.
    // this is covered by test/standalone/test-issue-36
    process.nextTick(function () {
      self.emit('close');
    });
  });
}

function cleanupOpenFiles(self) {
  self.openedFiles.forEach(function (internalFile) {
    // since fd slicer autoClose is true, destroying the only write stream
    // is guaranteed by the API to close the fd
    internalFile.ws.destroy();

    fs.unlink(internalFile.publicFile.path, function (err) {
      if (err) self.handleError(err);
    });
  });
  self.openedFiles = [];
}

function holdEmitQueue(self, eventEmitter) {
  var item = {cb: null, ee: eventEmitter, err: null};
  self.emitQueue.push(item);
  return function (cb) {
    item.cb = cb;
    flushEmitQueue(self);
  };
}

function errorEventQueue(self, eventEmitter, err) {
  var items = self.emitQueue.filter(function (item) {
    return item.ee === eventEmitter;
  });

  if (items.length === 0) {
    eventEmitter.emit('error', err);
    return;
  }

  items.forEach(function (item) {
    item.err = err;
  });
}

function flushEmitQueue(self) {
  while (self.emitQueue.length > 0 && self.emitQueue[0].cb) {
    var item = self.emitQueue.shift();

    // invoke the callback
    item.cb();

    if (item.err) {
      // emit the delayed error
      item.ee.emit('error', item.err);
    }
  }
}

function handlePart(self, partStream) {
  beginFlush(self);
  var emitAndReleaseHold = holdEmitQueue(self, partStream);
  partStream.on('end', function () {
    endFlush(self);
  });
  emitAndReleaseHold(function () {
    self.emit('part', partStream);
  });
}

function handleFile(self, fileStream) {
  if (self.error) return;
  var publicFile = {
    fieldName: fileStream.name,
    originalFilename: fileStream.filename,
    path: uploadPath(self.uploadDir, fileStream.filename),
    headers: fileStream.headers,
    size: 0
  };
  var internalFile = {
    publicFile: publicFile,
    ws: null
  };
  beginFlush(self); // flush to write stream
  var emitAndReleaseHold = holdEmitQueue(self, fileStream);
  fileStream.on('error', function (err) {
    self.handleError(err);
  });
  fs.open(publicFile.path, 'wx', function (err, fd) {
    if (err) return self.handleError(err);
    var slicer = fdSlicer.createFromFd(fd, {autoClose: true});

    // end option here guarantees that no more than that amount will be written
    // or else an error will be emitted
    internalFile.ws = slicer.createWriteStream({
      end: self.maxFilesSize - self.totalFileSize});

    // if an error ocurred while we were waiting for fs.open we handle that
    // cleanup now
    self.openedFiles.push(internalFile);
    if (self.error) return cleanupOpenFiles(self);

    var prevByteCount = 0;
    internalFile.ws.on('error', function (err) {
      if (err.code === 'ETOOBIG') {
        err = createError(413, err.message);
        err.code = 'ETOOBIG';
      }
      self.handleError(err);
    });
    internalFile.ws.on('progress', function () {
      publicFile.size = internalFile.ws.bytesWritten;
      var delta = publicFile.size - prevByteCount;
      self.totalFileSize += delta;
      prevByteCount = publicFile.size;
    });
    slicer.on('close', function () {
      if (self.error) return;
      emitAndReleaseHold(function () {
        self.emit('file', fileStream.name, publicFile);
      });
      endFlush(self);
    });
    fileStream.pipe(internalFile.ws);
  });
}

function handleField(self, fieldStream) {
  var value = '';
  var decoder = new StringDecoder(self.encoding);

  beginFlush(self);
  var emitAndReleaseHold = holdEmitQueue(self, fieldStream);
  fieldStream.on('error', function (err) {
    self.handleError(err);
  });
  fieldStream.on('readable', function () {
    var buffer = fieldStream.read();
    if (!buffer) return;

    self.totalFieldSize += buffer.length;
    if (self.totalFieldSize > self.maxFieldsSize) {
      self.handleError(createError(413,
        'maxFieldsSize ' + self.maxFieldsSize + ' exceeded'));
      return;
    }
    value += decoder.write(buffer);
  });

  fieldStream.on('end', function () {
    emitAndReleaseHold(function () {
      self.emit('field', fieldStream.name, value);
    });
    endFlush(self);
  });
}

function clearPartVars(self) {
  self.partHeaders = {};
  self.partName = null;
  self.partFilename = null;
  self.partTransferEncoding = 'binary';
  self.destStream = null;

  self.headerFieldDecoder = new StringDecoder(self.encoding);
  self.headerField = '';
  self.headerValueDecoder = new StringDecoder(self.encoding);
  self.headerValue = '';
}

function setUpParser(self, boundary) {
  self.boundary = new Buffer(boundary.length + 4);
  self.boundary.write('\r\n--', 0, boundary.length + 4, 'ascii');
  self.boundary.write(boundary, 4, boundary.length, 'ascii');
  self.lookbehind = new Buffer(self.boundary.length + 8);
  self.state = START;
  self.boundaryChars = {};
  for (var i = 0; i < self.boundary.length; i++) {
    self.boundaryChars[self.boundary[i]] = true;
  }

  self.index = null;
  self.partBoundaryFlag = false;

  beginFlush(self);
  self.on('finish', function () {
    if (self.state !== END) {
      self.handleError(createError(400, 'stream ended unexpectedly'));
    }
    endFlush(self);
  });
}

function uploadPath(baseDir, filename) {
  var ext = path.extname(filename).replace(FILE_EXT_RE, '$1');
  var name = randoString(18) + ext;
  return path.join(baseDir, name);
}

function randoString(size) {
  return rando(size).toString('base64').replace(/[\/\+]/g, function (x) {
    return b64Safe[x];
  });
}

function rando(size) {
  try {
    return crypto.randomBytes(size);
  } catch (err) {
    return crypto.pseudoRandomBytes(size);
  }
}

function parseFilename(headerValue) {
  var m = headerValue.match(/\bfilename="(.*?)"($|; )/i);
  if (!m) {
    m = headerValue.match(/\bfilename\*=utf-8\'\'(.*?)($|; )/i);
    if (m) {
      m[1] = decodeURI(m[1]);
    } else {
      return;
    }
  }

  var filename = m[1];
  filename = filename.replace(/%22|\\"/g, '"');
  filename = filename.replace(/&#([\d]{4});/g, function (m, code) {
    return String.fromCharCode(code);
  });
  return filename.substr(filename.lastIndexOf('\\') + 1);
}

function lower(c) {
  return c | 0x20;
}

function createError(status, message) {
  var error = new Error(message);
  Error.captureStackTrace(error, createError);
  error.status = status;
  error.statusCode = status;
  return error;
}
