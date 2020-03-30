import React from "react";
// import { URLS } from "../urls.js";
const URLS = {
  backendQuestions: "http://localhost:4040/api/questions"
};

class ImageBlock extends React.Component {
  constructor(props, context) {
    super(props, context);
    this.state = {
      editMode: false,
      image: ""
    };
  }

  componentDidMount() {
    let self = this;
    this.reader = new FileReader();
    this.reader.addEventListener(
      "load",
      function(result) {
        self.save(result.srcElement["result"]);
      },
      false
    );
  }

  handleClick = e => {
    if (this.state.editMode) {
      return;
    }
    this.setState(
      {
        editMode: true,
        url: this.props.contentState
          .getEntity(this.props.block.getEntityAt(0))
          .getData()["url"]
      },
      this.startEdit
    );
  };

  finishEdit = newContentState => {
    this.props.blockProps.onFinishEdit(
      this.props.block.getKey(),
      newContentState
    );
  };
  startEdit = () => {
    this.props.blockProps.onStartEdit(this.props.block.getKey());
  };

  handleSaveClick = e => {
    this.uploadImage(this.file);
  };

  save = url => {
    var entityKey = this.props.block.getEntityAt(0);
    var newContentState = this.props.contentState.mergeEntityData(entityKey, {
      url: url
    });
    this.setState(
      {
        editMode: false,
        url: null
      },
      this.finishEdit.bind(this, newContentState)
    );
  };

  cancel = e => {
    this.setState({
      editMode: false,
      url: null
    });
  };
  remove = e => {
    this.props.blockProps.onRemove(this.props.block.getKey());
  };
  handleFileChange = e => {
    this.file = e.target.files && e.target.files[0] ? e.target.files[0] : null;
  };
  randomName = () => {
    function makeid() {
      var text = "";
      var possible =
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";

      for (var i = 0; i < 5; i++)
        text += possible.charAt(Math.floor(Math.random() * possible.length));

      return text;
    }
    return makeid() + Date.now();
  };

  uploadImage = file => {
    const token = localStorage.getItem("token");
    fetch(
      URLS.backendQuestions +
        "/get-question-image-upload-policy?name=" +
        file.name,
      {
        method: "GET",
        headers: {
          Accept: "application/json",
          "Content-Type": "application/json",
          Authorization: "Token " + token
        }
      }
    )
      .then(res => res.json())
      .then(({ policy, success }) => {
        if (success) {
          const fullURL = policy.url + "/" + policy.fields.key;
          const formData = new FormData();
          Object.keys(policy.fields).forEach(key => {
            const value = policy.fields[key];
            formData.append(key, value);
          });
          formData.append("file", file);
          fetch(policy.url, {
            method: "POST",
            headers: {},
            body: formData
          }).then(() => {
            this.save(fullURL);
          });
        } else {
          alert("Some error occurred while uploading image");
        }
      });
    // this.reader.readAsDataURL(file)
  };

  render() {
    const { editMode } = this.state;
    var url;
    if (editMode) {
      url = this.state.url;
    } else {
      url = this.props.contentState
        .getEntity(this.props.block.getEntityAt(0))
        .getData()["url"];
    }
    return (
      <div onClick={this.handleClick} style={{ textAlign: "center" }}>
        {editMode ? (
          <div>
            <div>
              Click here to upload image
              <input
                onChange={this.handleFileChange}
                type="file"
                accept="image/*"
              />
            </div>
            <div>
              <button onClick={this.handleSaveClick}>Save</button>
              <button onClick={this.cancel}>Cancel</button>
              <button onClick={this.remove}>Remove</button>
            </div>
          </div>
        ) : null}
        <div>{url ? <img src={url} /> : <span>No image uploaded</span>}</div>
      </div>
    );
  }
}

export default ImageBlock;
